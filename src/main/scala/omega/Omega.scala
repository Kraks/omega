package omega

import scala.math._
import scala.util.Random

object Utils {
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
    if (ints.size < 1) 1
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
    if (r > -(r-b)) r - b
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

  def newVar(): String = {
    "x" + Random.nextInt(100).toString
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

  def getCoefficient(x: String): Int = {
    coefficients(vars.indexOf(x))
  }

  def removeVar(x: String): (List[Int], List[String]) = {
    removeVarByIdx(vars.indexOf(x))
  }

  def removeVarByIdx(idx: Int): (List[Int], List[String]) = {
    val newCoefs = removeByIdx(coefficients, idx)
    val newVars = removeByIdx(vars, idx)
    (newCoefs, newVars)
  }

  def _subst(x: String, term: (List[Int], List[String])): (List[Int], List[String]) = {
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
    minWithIndex(coefficients.tail)(Ordering.by((x:Int) => abs(x))) 
  }
}

// Linear Equality: \Sigma a_i x_i = 0 where x_0 = 1 (here uses 
// "_" stands for that variable)
case class EQ(coefficients: List[Int], vars: List[String]) 
  extends Constraint(coefficients, vars) {

  override def normalize(): Option[EQ] = {
    val g = gcd(coefficients.tail)
    if (coefficients.head % g == 0) {
      Some(EQ(coefficients.map(_ / g), vars))
    }
    // If the constant term a_0 can not be evenly divided by g, 
    // then there is no integer solution, returns None
    else None
  }
  
  override def toString(): String = { toStringPartially() + " = 0" }
  
  def getFirstAtomicVar(): Option[(Int, String)] = {
    for (((c,x), idx) <- (coefficients zip vars).zipWithIndex) {
      if (abs(c) == 1) return Some((idx, x))
    }
    return None
  }

  def getEquationBy(x: String): (List[Int], List[String]) = {
    getEquationBy(vars.indexOf(x))
  }

  def getEquationBy(idx: Int): (List[Int], List[String]) = {
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
    val g = gcd(coefficients.tail)
    if (coefficients.head % g == 0) {
      Some(GEQ(coefficients.map(_ / g), vars))
    }
    // If the constant term a_0 can not be evenly divided by g,
    // then take floors of a_0/g, which tightens the inequality
    else {
      val a0 = floor(coefficients.head.toDouble / g).toInt
      Some(GEQ(a0::coefficients.tail.map(_ / g), vars))
    }
  }
  
  override def toString(): String = { toStringPartially() + " >= 0" }

  override def subst(x: String, term: (List[Int], List[String])): GEQ = {
    val (c, v) = _subst(x, term)
    GEQ(c, v)
  }
}

case class Problem(cs: List[Constraint]) {

  def getAllEqualities(): List[EQ] = {
    cs.filter(_.isInstanceOf[EQ]).asInstanceOf[List[EQ]]
  }

  def partition(): (List[EQ], List[GEQ]) = {
    val (eqs, geqs) = cs.partition(_.isInstanceOf[EQ])
    (eqs.asInstanceOf[List[EQ]], geqs.asInstanceOf[List[GEQ]])
  }

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
    def eliminate(eqs: List[EQ], geqs: List[GEQ]) {
      if (eqs.nonEmpty) {
        val eq = eqs.head
        //if exists some var with 1/-1 coef then subst all others
        //  aux(eqs.tail.map(_.subst ...), geqs.map(_.subst ...))
        //else find a smallest coef
        //  
      }
      geqs
    }
    ???
  }

}

object Main extends App {
  println("Omega Test")

  println("3 mod_hat 2 = " + Utils.mod_hat(3, 2))
  println("5 mod_hat 2 = " + Utils.mod_hat(5, 2))
  println("-5 mod_hat 2 = " + Utils.mod_hat(-5, 2))

  println("12 mod_hat 8 = " + Utils.mod_hat(12, 8))
  println("12 mod_hat2 8 = " + Utils.mod_hat2(12, 8))

  println("3 / 2 = " + Utils.int_div(3, 2))
  println("5 / 2 = " + Utils.int_div(5, 2))
  println("-5 / 2 = " + Utils.int_div(-5, 2))

  val eq1 = EQ(List(1, 2, -3), 
               List("_", "a", "b"))
  val eq2 = EQ(List(3, 1, 5),
               List("_", "b", "a"))

  val cv = eq2.getEquationBy("b")
  println(eq1.subst("b", cv))
}


