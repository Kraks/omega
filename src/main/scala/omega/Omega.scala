package omega

import scala.math._
import scala.util.Random

object Utils {
  val const = "_"

  private def gcd_aux(a: Int, b: Int): Int = {
    assert(a >= 0 && b >= 0)
    if (b == 0) a else gcd_aux(b, a % b)
  }

  def gcd(a: Int, b: Int): Int = {
    val a1 = if (a < 0) abs(a) else a
    val b1 = if (b < 0) abs(b) else b
    gcd_aux(a1, b1)
  }

  def gcd(ints: List[Int]): Int = {
    if (ints.size == 0) 1
    else if (ints.size == 1) gcd(ints.head, ints.head)
    else ints.reduce((x, y) => gcd(x, y))
  }

  def sign(x: Int): Int = {
    if (x > 0) 1
    else if (x < 0) -1
    else 0
  }

  def int_div(a: Int, b: Int): Int = {
    assert(b > 0)
    if (a > 0) a / b
    else -((-a + b - 1) / b)
  }
  
  /* This version is extracted from the C/C++ implementation of omega */
  def mod_hat2(a: Int, b: Int): Int = {
    assert(b > 0)
    val r = a - b * int_div(a, b)
    //if (r > -(r-b)) r - b
    if (r >= -(r-b)) r - b // a slightly change to make mod_hat behaves as the paper 
    else r
  }
  
  /* This version follows the description of original paper */
  def mod_hat(a: Int, b: Int): Int = {
    assert(b > 0)
    if (a % b > b / 2) a % b
    else (a % b) - b
  }

  def removeByIdx[T](lst: List[T], idx: Int): List[T] = {
    lst.take(idx) ++ lst.drop(idx+1)
  }

  def minWithIndex[T](lst: List[T])(implicit ordering: Ordering[T]): (T,Int) = {
    lst.zipWithIndex.reduce[(T,Int)]({
      case ((minv,mini), (x,i)) => if (ordering.lt(x,minv)) (x,i) else (minv, mini)
    })
  }
  
}

import Utils._

abstract class Constraint(coefficients: List[Int], vars: List[String])  {
  def normalize(): Option[Constraint]

  def subst(x: String, term: (List[Int], List[String])): Constraint

  def toStringPartially(): String = {
    val s = coefficients.head.toString
    (coefficients.tail zip vars.tail).foldLeft(s)({
      case (acc, (c,v)) => 
        val cstr = if (c > 0) " + " + c.toString
                   else " - " + abs(c).toString
        val cvstr = cstr + v
        acc + cvstr
    })
  }

  def removeZeroCoef(coefs: List[Int], vars: List[String]): (List[Int], List[String]) = {
    val cvpairs = for ((c, v) <- (coefs zip vars) if !(c == 0 && v != const)) yield (c, v)
    // TODO: refactor this to only use one pass
    (cvpairs.map(_._1), cvpairs.map(_._2))
  }

  def getCoefficient(x: String): Int = {
    coefficients(vars.indexOf(x))
  }

  def getVarByIdx(i: Int): String = { vars(i) }

  def removeVar(x: String): (List[Int], List[String]) = {
    removeVarByIdx(vars.indexOf(x))
  }

  def removeVarByIdx(idx: Int): (List[Int], List[String]) = {
    val newCoefs = removeByIdx(coefficients, idx)
    val newVars = removeByIdx(vars, idx)
    (newCoefs, newVars)
  }
  
  //TODO: rename this
  def _subst(x: String, term: (List[Int], List[String])): (List[Int], List[String]) = {
    if (!vars.contains(x)) {
      return (coefficients, vars)
    }
    val c = getCoefficient(x)
    val (oldCoefs, oldVars) = removeVar(x)
    val newCoefs = term._1.map(_ * c)
    val newVars = term._2
    val g = ((oldCoefs++newCoefs) zip (oldVars++newVars)).groupBy(_._2).values.map({
      cvs => cvs.reduce((acc, cv) => (acc._1 + cv._1, cv._2))
    }).toList.sortWith(_._2 < _._2)
    (g.map(_._1), g.map(_._2))
  }
  
  // returns (value, index)
  def minCoef(): (Int, Int) = { 
    val (v, idx) = minWithIndex(coefficients.tail)(Ordering.by((x:Int) => abs(x))) 
    (v, idx+1)
  }
}

// Linear Equality: \Sigma a_i x_i = 0 where x_0 = 1 (here uses 
// "_" stands for that variable)
case class EQ(coefficients: List[Int], vars: List[String]) 
  extends Constraint(coefficients, vars) {

  override def normalize(): Option[EQ] = {
    val g = gcd(coefficients.tail)
    if (coefficients.head % g == 0) {
      val coefs = coefficients.map(_ / g)
      // Also remove items whose coefficient is 0
      val (newCoefs, newVars) = removeZeroCoef(coefs, vars)
      Some(EQ(newCoefs, newVars))
    }
    // If the constant term a_0 can not be evenly divided by g, 
    // then there is no integer solution, returns None
    else None
  }
  
  override def toString(): String = { toStringPartially() + " = 0" }
  
  // An atmoic variable which has coefficient of 1 or -1
  // returns (index, var)
  def getFirstAtomicVar(): Option[(Int, String)] = {
    for (((c,x), idx) <- (coefficients.tail zip vars.tail).zipWithIndex) {
      if (abs(c) == 1) return Some((idx+1, x))
    }
    return None
  }

  def getEquation(x: String): (List[Int], List[String]) = {
    getEquation(vars.indexOf(x))
  }

  def getEquation(idx: Int): (List[Int], List[String]) = {
    assert(idx != 0)
    assert(abs(coefficients(idx)) == 1)
    val (coefs, vars) = removeVarByIdx(idx)
    (coefs.map(_ * -1), vars)
  }
  
  override def subst(x: String, term: (List[Int], List[String])): EQ = {
    val (c, v)= _subst(x, term)
    EQ(c, v)
  }
}

// Linear Inequality: \Sigma a_i x_i >= 0 where x_0 = 1
case class GEQ(coefficients: List[Int], vars: List[String]) 
  extends Constraint(coefficients, vars) {
  
  override def normalize(): Option[GEQ] = {
    //TODO: may need to review this
    val g = gcd(coefficients.tail)
    val coefs = if (coefficients.head % g == 0) { coefficients.map(_ / g) }
    // If the constant term a_0 can not be evenly divided by g,
    // then take floors of a_0/g, which tightens the inequality
    else {
      //val a0 = coefficients.head / g
      val a0 = floor(coefficients.head.toDouble / g).toInt
      a0::coefficients.tail.map(_ / g)
    }
    // Also remove items whose coefficient is 0
    val (newCoefs, newVars) = removeZeroCoef(coefs, vars)
    Some(GEQ(newCoefs, newVars))
  }
  
  override def toString(): String = { toStringPartially() + " >= 0" }

  override def subst(x: String, term: (List[Int], List[String])): GEQ = {
    val (c, v) = _subst(x, term)
    GEQ(c, v)
  }

  def contradict(that: GEQ): Boolean = {
    val thisConst = coefficients.head
    val thatConst = that.coefficients.head
    val thisCoefs = coefficients.tail
    val thatCoefs = that.coefficients.tail
    //TODO: check zero coefs
    vars == that.vars &&
    (thisCoefs zip thatCoefs).foldLeft(true)({
      case (b, (c1,c2)) => b && abs(c1) == abs(c2) && (sign(c1)+sign(c2)==0)
    }) 
  }
}

case class Problem(cs: List[Constraint]) {
  var varIdx = 0
  val greeks = List("α", "β", "γ", "δ", "ϵ", "ζ", "η", "θ", "ι", "κ", "λ", "μ",
                    "ν", "ξ", "ο", "π", "ρ", "σ", "τ", "υ", "ϕ", "χ", "ψ", "ω")
  //TODO: refactor this
  def generateNewVar(): String = {
    //"α_" + Random.nextInt(100).toString
    val oldIdx = varIdx
    varIdx += 1
    greeks(oldIdx)
  }

  def getEqualities(): List[EQ] = {
    cs.filter(_.isInstanceOf[EQ]).asInstanceOf[List[EQ]]
  }

  def partition(): (List[EQ], List[GEQ]) = {
    val (eqs, geqs) = cs.partition(_.isInstanceOf[EQ])
    (eqs.asInstanceOf[List[EQ]], geqs.asInstanceOf[List[GEQ]])
  }

  override def toString(): String = { "{ " + cs.mkString("\n  ") + " }" }

  /* A constraint is normalized if all coefficients are integers, and the
   * greatest common divisor of the coefficients (not including a_0) is 1.
   */
  def normalize(): Option[Problem] = {
    val newCs = for (c <- cs) yield 
      c.normalize match {
        case None => return None
        case Some(c) => c
      }
    Some(Problem(newCs))
  }
  
  def eliminateEQs(): Problem = {
    val (eqs, geqs) = partition()
    def eliminate(eqs: List[EQ], geqs: List[GEQ]): List[GEQ] = {
      if (eqs.nonEmpty) {
        val eq = eqs.head

        println("current constraints:")
        for (eq <- (eqs++geqs)) { println(s"  $eq") }

        eq.getFirstAtomicVar match {
          case None =>
            val (ak, idx) = eq.minCoef
            val xk = eq.getVarByIdx(idx)
            val sign_ak = sign(ak)
            val m = abs(ak) + 1
            val v = generateNewVar
            val (coefs, vars) = eq.removeVarByIdx(idx)
            val newCoefs = coefs.map((c: Int) => sign_ak * (mod_hat2(c, m))) ++ List(-1*sign_ak*m)
            val newVars = vars ++ List(v)
            val substTerm = (newCoefs, newVars)
            
            /* Debug */
            val substStr = EQ(newCoefs, newVars).toStringPartially
            //println(s"choose ak: $ak, xk: $xk")
            println(s"subst: $xk = $substStr")
            /* Debug */

            eliminate(eq.subst(xk, substTerm).normalize.get::eqs.tail.map(_.subst(xk, substTerm)),
                      geqs.map(_.subst(xk, substTerm)))

          case Some((idx, x)) =>
            val term = eq.getEquation(idx)
            /* Debug */
            val substStr = EQ(term._1, term._2).toStringPartially
            println(s"subst: $x = $substStr")
            /* Debug */
            
            eliminate(eqs.tail.map(_.subst(x, term)), geqs.map(_.subst(x, term)))
        }
      }
      else { geqs }
    }
    Problem(eliminate(eqs, geqs))
  }

  def contradict(): Boolean = {
    ???
  }

}

object Main extends App {
  println("Omega Test")

  println("3 / 2 = " + Utils.int_div(3, 2))
  println("5 / 2 = " + Utils.int_div(5, 2))
  println("-5 / 2 = " + Utils.int_div(-5, 2))

  println("3 mod_hat2 2 = " + Utils.mod_hat2(3, 2))
  println("5 mod_hat2 2 = " + Utils.mod_hat2(5, 2))
  println("-5 mod_hat2 2 = " + Utils.mod_hat2(-5, 2))

  println("12 mod_hat2 8 = " + Utils.mod_hat2(12, 8))
  println("12 mod_hat 8 = " + Utils.mod_hat(12, 8))

  ///////////////////////////////

  val eq1 = EQ(List(1, 2, -3), 
               List("_", "a", "b"))
  val eq2 = EQ(List(3, 1, 5),
               List("_", "b", "a"))
  val p1 = Problem(List(eq2, eq1))
  println(p1)
  //val p1elim = p1.eliminateEQs
  //println("after elimination: " + p1elim)

  ///////////////////////////////

  val eq3 = EQ(List(-17, 7, 12, 31), List(const, "x", "y", "z"))
  val eq4 = EQ(List(-7,  3, 5,  14), List(const, "x", "y", "z"))
  val p2 = Problem(List(eq3, eq4)).normalize.get
  println(p2)
  val p2elim = p2.eliminateEQs
  println(p2elim)
  
  val ineq1 = GEQ(List(-1, 1), List(const, "x"))
  val ineq2 = GEQ(List(40, -1), List(const, "x"))
  //println(ineq2.normalize.get)
  val ineq3 = GEQ(List(50, 1), List(const, "y"))
  val ineq4 = GEQ(List(50, -1), List(const, "y"))
  val p3 = Problem(List(eq3, eq4, ineq1, ineq2, ineq3, ineq4))
  println(p3)
  val p3elim = p3.eliminateEQs.normalize.get
  println(p3elim)

  val ineq5 = GEQ(List(11, 13), List(const, "a")).normalize.get
  println(ineq5)
  val ineq6 = GEQ(List(28, -13), List(const, "a")).normalize.get
  println(ineq6)

  val ineq7 = GEQ(List(-2, 3, 5), List(const, "x", "y"))
  val ineq8 = GEQ(List(0, -3,-5), List(const, "x", "y"))
  println(s"contradict: ${ineq7.contradict(ineq8)}")
}

