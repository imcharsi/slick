package scala.slick.lifted

import scala.language.higherKinds
import scala.language.experimental.macros
import scala.annotation.implicitNotFound
import scala.collection.generic.CanBuild
import scala.reflect.ClassTag
import scala.reflect.macros.Context
import scala.slick.ast.{Join => AJoin, _}
import FunctionSymbolExtensionMethods._
import ScalaBaseType._

/** An instance of Query represents a query or view, i.e. a computation of a
  * collection type (Rep[Seq[T]]). It is parameterized with both, the mixed
  * type (the type of values you see e.g. when you call map()) and the unpacked
  * type (the type of values that you get back when you run the query).  */
sealed abstract class Query[+E, U, C[_]] extends Rep[C[U]] { self =>

  def shaped: ShapedValue[_ <: E, U]
  final lazy val packed = shaped.toNode

  def flatMap[F, T, D[_]](f: E => Query[F, T, D]): Query[F, T, C] = {
    val generator = new AnonSymbol
    val aliased = shaped.encodeRef(generator :: Nil).value
    val fv = f(aliased)
    new WrappingQuery[F, T, C](new Bind(generator, toNode, fv.toNode), fv.shaped)
  }

  def map[F, G, T](f: E => F)(implicit shape: Shape[_ <: ShapeLevel.Flat, F, T, G]): Query[G, T, C] =
    flatMap(v => Query[F, T, G](f(v)))

  def >>[F, T, D[_]](q: Query[F, T, D]): Query[F, T, C] = flatMap(_ => q)

  def filter[T](f: E => T)(implicit wt: CanBeQueryCondition[T]): Query[E, U, C] = {
    val generator = new AnonSymbol
    val aliased = shaped.encodeRef(generator :: Nil)
    val fv = f(aliased.value)
    new WrappingQuery[E, U, C](Filter.ifRefutable(generator, toNode, wt(fv).toNode), shaped)
  }

  def withFilter[T : CanBeQueryCondition](f: E => T) = filter(f)

  def where[T <: Column[_] : CanBeQueryCondition](f: E => T) = filter(f)

  def join[E2, U2, D[_]](q2: Query[E2, U2, D], jt: JoinType = JoinType.Inner) = {
    val leftGen, rightGen = new AnonSymbol
    val aliased1 = shaped.encodeRef(leftGen :: Nil)
    val aliased2 = q2.shaped.encodeRef(rightGen :: Nil)
    new BaseJoinQuery[E, E2, U, U2, C](leftGen, rightGen, toNode, q2.toNode, jt, aliased1.zip(aliased2))
  }
  def innerJoin[E2, U2, D[_]](q2: Query[E2, U2, D]) = join(q2, JoinType.Inner)
  def leftJoin[E2, U2, D[_]](q2: Query[E2, U2, D]) = join(q2, JoinType.Left)
  def rightJoin[E2, U2, D[_]](q2: Query[E2, U2, D]) = join(q2, JoinType.Right)
  def outerJoin[E2, U2, D[_]](q2: Query[E2, U2, D]) = join(q2, JoinType.Outer)
  def zip[E2, U2, D[_]](q2: Query[E2, U2, D]): Query[(E, E2), (U, U2), C] = join(q2, JoinType.Zip)
  def zipWith[E2, U2, F, G, T, D[_]](q2: Query[E2, U2, D], f: (E, E2) => F)(implicit shape: Shape[_ <: ShapeLevel.Flat, F, T, G]): Query[G, T, C] =
    join(q2, JoinType.Zip).map[F, G, T](x => f(x._1, x._2))
  def zipWithIndex = {
    val leftGen, rightGen = new AnonSymbol
    val aliased1 = shaped.encodeRef(leftGen :: Nil)
    val aliased2 = ShapedValue(Column.forNode[Long](Ref(rightGen)), Shape.columnShape[Long, ShapeLevel.Flat])
    new BaseJoinQuery[E, Column[Long], U, Long, C](leftGen, rightGen, toNode, RangeFrom(0L), JoinType.Zip, aliased1.zip(aliased2))
  }

  def sortBy[T <% Ordered](f: E => T): Query[E, U, C] = {
    val generator = new AnonSymbol
    val aliased = shaped.encodeRef(generator :: Nil)
    new WrappingQuery[E, U, C](SortBy(generator, toNode, f(aliased.value).columns), shaped)
  }

  def sorted(implicit ev: (E => Ordered)): Query[E, U, C] = sortBy(identity)

  def groupBy[K, T, G, P](f: E => K)(implicit kshape: Shape[_ <: ShapeLevel.Flat, K, T, G], vshape: Shape[_ <: ShapeLevel.Flat, E, _, P]): Query[(G, Query[P, U, Seq]), (T, Query[P, U, Seq]), C] = {
    val sym = new AnonSymbol
    val key = ShapedValue(f(shaped.encodeRef(sym :: Nil).value), kshape).packedValue
    val value = ShapedValue(pack.as[Seq], Shape.repShape.asInstanceOf[Shape[ShapeLevel.Flat, Query[P, U, Seq], Query[P, U, Seq], Query[P, U, Seq]]])
    val group = GroupBy(sym, toNode, key.toNode)
    new WrappingQuery[(G, Query[P, U, Seq]), (T, Query[P, U, Seq]), C](group, key.zip(value))
  }

  def encodeRef(path: List[Symbol]): Query[E, U, C] = new Query[E, U, C] {
    val shaped = self.shaped.encodeRef(path)
    lazy val toNode = Path(path)
  }

  def union[O >: E, R, D[_]](other: Query[O, U, D]) =
    new WrappingQuery[O, U, C](Union(toNode, other.toNode, false), shaped)

  def unionAll[O >: E, R, D[_]](other: Query[O, U, D]) =
    new WrappingQuery[O, U, C](Union(toNode, other.toNode, true), shaped)

  def ++[O >: E, R, D[_]](other: Query[O, U, D]) = unionAll(other)

  def length: Column[Int] = Library.CountAll.column(toNode)
  def countDistinct: Column[Int] = Library.CountDistinct.column(toNode)
  def exists = Library.Exists.column[Boolean](toNode)

  def pack[R](implicit packing: Shape[_ <: ShapeLevel.Flat, E, _, R]): Query[R, U, C] =
    new Query[R, U, C] {
      val shaped: ShapedValue[_ <: R, U] = self.shaped.packedValue(packing)
      def toNode = self.toNode
    }

  def as[D[X] <: Iterable[X]](implicit cbf: CanBuild[Any, D[Any]], tag: ClassTag[D[_]]): Query[E, U, D] = new Query[E, U, D] {
    val shaped = self.shaped
    def toNode = CollectionCast(self.toNode, CollectionTypeConstructor.forColl[D])
  }

  def take(num: Int): Query[E, U, C] = new WrappingQuery[E, U, C](Take(toNode, num), shaped)
  def drop(num: Int): Query[E, U, C] = new WrappingQuery[E, U, C](Drop(toNode, num), shaped)
}

object Query {
  def apply[E, U, R](value: E)(implicit unpack: Shape[_ <: ShapeLevel.Flat, E, U, R]): Query[R, U, Seq] = {
    val shaped = ShapedValue(value, unpack).packedValue
    new WrappingQuery[R, U, Seq](Pure(shaped.toNode), shaped)
  }

  def empty: Query[Unit, Unit, Seq] = new Query[Unit, Unit, Seq] {
    val toNode = shaped.toNode
    def shaped = ShapedValue((), Shape.unitShape[ShapeLevel.Flat])
  }
}

@implicitNotFound("Type ${T} cannot be a query condition (only Boolean, Column[Boolean] and Column[Option[Boolean]] are allowed")
trait CanBeQueryCondition[-T] extends (T => Column[_])

object CanBeQueryCondition {
  implicit object BooleanColumnCanBeQueryCondition extends CanBeQueryCondition[Column[Boolean]] {
    def apply(value: Column[Boolean]) = value
  }
  implicit object BooleanOptionColumnCanBeQueryCondition extends CanBeQueryCondition[Column[Option[Boolean]]] {
    def apply(value: Column[Option[Boolean]]) = value
  }
  implicit object BooleanCanBeQueryCondition extends CanBeQueryCondition[Boolean] {
    def apply(value: Boolean) = new LiteralColumn(value)
  }
}

class WrappingQuery[+E, U, C[_]](val toNode: Node, val base: ShapedValue[_ <: E, U]) extends Query[E, U, C] {
  lazy val shaped = base.encodeRef(toNode.nodeIntrinsicSymbol :: Nil)
}

final class BaseJoinQuery[+E1, +E2, U1, U2, C[_]](leftGen: Symbol, rightGen: Symbol, left: Node, right: Node, jt: JoinType, base: ShapedValue[_ <: (E1, E2), (U1, U2)])
    extends WrappingQuery[(E1, E2), (U1,  U2), C](AJoin(leftGen, rightGen, left, right, jt, LiteralNode(true)), base) {
  def on[T <: Column[_]](pred: (E1, E2) => T)(implicit wt: CanBeQueryCondition[T]): Query[(E1, E2), (U1, U2), C] =
    new WrappingQuery[(E1, E2), (U1, U2), C](AJoin(leftGen, rightGen, left, right, jt, wt(pred(base.value._1, base.value._2)).toNode), base)
}

/** Represents a database table. Profiles add extension methods to TableQuery
  * for operations that can be performed on tables but not on arbitrary
  * queries, e.g. getting the table DDL. */
final class TableQuery[+E <: AbstractTable[_], U](val shaped: ShapedValue[_ <: E, U]) extends Query[E, U, Seq] {
  val toNode = shaped.toNode

  /** Get the "raw" table row that represents the table itself, as opposed to
    * a Path for a variable of the table's type. This method should generally
    * not be called from user code. */
  def baseTableRow: E = shaped.value
}

object TableQuery {
  def apply[E <: AbstractTable[_]](cons: Tag => E): TableQuery[E, E#TableElementType] = {
    val baseTable = cons(new BaseTag { base =>
      def taggedAs(path: List[Symbol]): AbstractTable[_] = cons(new RefTag(path) {
        def taggedAs(path: List[Symbol]) = base.taggedAs(path)
      })
    })
    new TableQuery[E, E#TableElementType](ShapedValue(baseTable, Shape.repShape.asInstanceOf[Shape[ShapeLevel.Flat, E, E#TableElementType, E]]))
  }

  def apply[E <: AbstractTable[_]]: TableQuery[E, E#TableElementType] =
    macro TableQueryMacroImpl.apply[E]
}

object TableQueryMacroImpl {

  def apply[E <: AbstractTable[_]](c: Context)(implicit e: c.WeakTypeTag[E]): c.Expr[TableQuery[E, E#TableElementType]] = {
    import c.universe._
    val cons = c.Expr[Tag => E](Function(
      List(ValDef(Modifiers(Flag.PARAM), newTermName("tag"), Ident(typeOf[Tag].typeSymbol), EmptyTree)),
      Apply(
        Select(New(TypeTree(e.tpe)), nme.CONSTRUCTOR),
        List(Ident(newTermName("tag")))
      )
    ))
    reify { TableQuery.apply[E](cons.splice) }
  }
}
