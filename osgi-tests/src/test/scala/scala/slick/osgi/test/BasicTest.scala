package scala.slick.osgi.test

import org.junit.Test
import org.junit.runner.RunWith
import org.junit.Assert._
import org.ops4j.pax.exam
import org.ops4j.pax.exam.junit.{Configuration, ExamReactorStrategy, JUnit4TestRunner}
import org.ops4j.pax.exam.spi.reactors.AllConfinedStagedReactorFactory
import scala.slick.SlickException
import scala.slick.osgi.testutil._

@RunWith(classOf[JUnit4TestRunner])
@ExamReactorStrategy(Array(classOf[AllConfinedStagedReactorFactory]))
class BasicTest extends SlickOsgiHelper {

  @Configuration
  def config(): Array[exam.Option] = {
    standardOptions
  }

  @Test
  def testPlainSQL: Unit = {
    import scala.slick.jdbc.JdbcBackend._
    import scala.slick.jdbc.StaticQuery.interpolation
    Database.forURL("jdbc:h2:mem:test-osgi") withSession { implicit session =>
      assertEquals("TEST-OSGI", sql"select {fn database()}".as[String].first)
    }
  }
}