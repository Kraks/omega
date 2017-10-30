package omega

import scala.math._
import scala.util.Random

import scala.collection._

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
    if (ints.length == 0) 1
    else if (ints.length == 1) gcd(ints.head, ints.head)
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

object Constraint {
  val const = "_"
}

import Utils._
import Constraint._

trait Constraint[C <: Constraint[C]] {
  val coefficients: List[Int]
  val vars: List[String]

  assert(coefficients.length == vars.length)
  assert(vars(0) == const)

  def normalize(): Option[Constraint[C]]

  def subst(x: String, term: (List[Int], List[String])): C

  def trivial: Boolean

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

  def getVars = vars.tail

  def getConstant = coefficients.head

  def getCoefficients = coefficients.tail

  def containsVar(x: String) = vars.contains(x)

  def getCoefficientByVar(x: String): Int = {
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

  def removeZeroCoef(coefs: List[Int], vars: List[String]): (List[Int], List[String]) = {
    val cvpairs = for ((c, v) <- (coefs zip vars) if !(c == 0 && v != const)) yield (c, v)
    // TODO: may refactor this to only use one pass
    (cvpairs.map(_._1), cvpairs.map(_._2))
  }
  
  /* Combines like terms and reorder the variables alphabetically.
   * The constant term placed at the first position.
   */
  def reorder(coefficients: List[Int], vars: List[String]): (List[Int], List[String]) = {
    val g = (coefficients zip vars).groupBy(_._2).values.map({
      cvs => cvs.reduce((acc, cv) => (acc._1 + cv._1, cv._2))
    }).toList.sortWith(_._2 < _._2)
    (g.map(_._1), g.map(_._2))
  }

  def scale(coefficients: List[Int], x: Int): List[Int] = { coefficients.map(_ * x) }
  
  //TODO: better rename this function
  def _subst(x: String, term: (List[Int], List[String])): (List[Int], List[String]) = {
    if (!vars.contains(x)) {
      return (coefficients, vars)
    }
    val c = getCoefficientByVar(x)
    val (oldCoefs, oldVars) = removeVar(x)
    val newVars = term._2
    val newCoefs = term._1.map(_ * c)
    reorder(oldCoefs++newCoefs, oldVars++newVars)
  }
  
  /* Finds the minimum absolute value of coefficient.
   * Returns ((value, var) index).
   */
  def minCoef(): ((Int, String), Int) = { 
    val (v, idx) = minWithIndex(coefficients.tail)(Ordering.by((x:Int) => abs(x))) 
    ((v, getVarByIdx(idx+1)), idx+1)
  }

  def noZeroCoef(): Boolean = { !coefficients.tail.contains(0) }
}

/* Linear Equality: \Sigma a_i x_i = 0 where x_0 = 1,
 * Here always uses "_" stands for x_0.
 */
case class EQ(coefficients: List[Int], vars: List[String]) extends Constraint[EQ] {

  /* Normalize the coefficients, which makes the gcd of coefficients 
   * is 1. If the constant term a_0 can not be evenly divided by g, 
   * then there is no integer solution, returns None.
   * Also remove items whose coefficient is 0.
   */
  override def normalize(): Option[EQ] = {
    val g = gcd(coefficients.tail)
    if (coefficients.head % g == 0) {
      val coefs = coefficients.map(_ / g)
      // Also remove items whose coefficient is 0
      val (newCoefs, newVars) = removeZeroCoef(coefs, vars)
      Some(EQ(newCoefs, newVars))
    }
    else None
  }
  
  override def toString(): String = { toStringPartially() + " = 0" }

  def trivial: Boolean = {
    vars.length == 1 && coefficients.length == 1 && coefficients.head == 0
  }
  
  /* Get the first atomic variable. 
   * An atmoic variable has coefficient of 1 or -1.
   * Returns (index, var)
   */
  def getFirstAtomicVar(): Option[(String, Int)] = {
    for (((c,x), idx) <- (coefficients.tail zip vars.tail).zipWithIndex) {
      if (abs(c) == 1) return Some((x, idx+1))
    }
    return None
  }

  /* Get the equation for an atomic variable x_k,
   * where x_k = a_i * x_i.
   * Returns a list of integers for a_i, and a list
   * of strings for x_i.
   */
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

/* Linear Inequality: \Sigma a_i x_i >= 0 where x_0 = 1
 */
case class GEQ(coefficients: List[Int], vars: List[String]) extends Constraint[GEQ] {
  
  override def toString(): String = { toStringPartially() + " >= 0" }

  /* Normalize the coefficients, which makes the gcd of coefficients 
   * is 1. If the constant term a_0 can not be evenly divided by g,
   * then take floors of a_0/g, which tightens the inequality.
   * Also remove items whose coefficient is 0.
   */
  override def normalize(): Option[GEQ] = {
    val g = gcd(coefficients.tail)
    val coefs = if (coefficients.head % g == 0) { coefficients.map(_ / g) }
    else {
      //val a0 = coefficients.head / g
      val a0 = floor(coefficients.head.toDouble / g).toInt
      a0::coefficients.tail.map(_ / g)
    }
    val (newCoefs, newVars) = removeZeroCoef(coefs, vars)
    Some(GEQ(newCoefs, newVars))
  }
  
  /* Substitute a variable with a linear term, which the term is a list
   * of integers (coefficients) and a list of strings (variables).
   */
  override def subst(x: String, term: (List[Int], List[String])): GEQ = {
    val (c, v) = _subst(x, term)
    GEQ(c, v)
  }


  /* Check if two geqs are contradictory.
   * e.g.,
   * -2 + 2x + 3y >= 0,  0 - 2x - 3y >= 0 are contraWithory, but
   *  0 + 2x + 3y >= 0,  2 - 2x - 3y >= 0 are not.
   * -5 + 2x + 3y >= 0, -9 - 2x - 3y >= 0 are contraWithory, but
   *  9 + 2x + 3y >= 0, -5 - 2x - 3y >= 0 are not.
   */
  def contraWith(that: GEQ): Boolean = {
    assert(noZeroCoef && that.noZeroCoef)

    val thisConst = coefficients.head
    val thatConst = that.coefficients.head
    val coefss = coefficients.tail zip that.coefficients.tail
    // variables of two inequalities should be the same
    vars == that.vars &&
    // coefficients of two inequalities should be additive inversed
    coefss.foldLeft(true)({
      case (b, (c1,c2)) => b && abs(c1)==abs(c2) && (sign(c1)+sign(c2)==0)
    }) &&
    // constant term should be consistant
    (-thisConst) > thatConst
  }
  
  /* If two geqs can form a tight equality, then return the equality,
   * otherwise returns None.
   * e.g., given 2x + 3y >= 6 and 2x + 3y <= 6, returns 2x + 3y = 6.
   */
  def tighten(that: GEQ): Option[EQ] = {
    assert(noZeroCoef && that.noZeroCoef)

    val canMerge = (vars == that.vars) &&
      (coefficients zip that.coefficients).foldLeft(true)({
        case (b, (c1,c2)) => b && abs(c1)==abs(c2) && (sign(c1)+sign(c2)==0)
      })
    if (canMerge) Some(EQ(coefficients, vars)) else None
  }

  /* If two geqs can be simplified as one, or say one can be inferred 
   * from another then returns Some(c), otherwise returns None
   * e.g., given x >= 5 and x >= 0, then return x >= 5
   * TODO: this requires two inequalities have the same coefficients,
   *       need to think about other cases
   */
  def subsume(that: GEQ): Option[GEQ] = {
    assert(noZeroCoef && that.noZeroCoef)

    val thisConst = coefficients.head
    val thatConst = that.coefficients.head
    if ((vars == that.vars) && (coefficients.tail == that.coefficients.tail))
      Some(GEQ(min(thisConst, thatConst)::coefficients.tail, vars))
    else None
  }
  
  /* Decides whether an inequality trivially holds, i.e., not variable involves,
   * and constant term is greater or equal than 0.
   */
  def trivial: Boolean = {
    vars.length == 1 && coefficients.length == 1 && coefficients.head >= 0
  }
  
  /* Join two inequalities and eliminate variable x.
   * The two inequalities should be a pair of upper bound and
   * lower bound of x, otherwise return None.
   */
  def join(that: GEQ, x: String): Option[GEQ] = {
    assert(containsVar(x) && that.containsVar(x))
    assert(noZeroCoef && that.noZeroCoef)

    val (thisCoefs, thisVars) = this.removeVar(x)
    val (thatCoefs, thatVars) = that.removeVar(x)
    val thisXCoef = this.getCoefficientByVar(x)
    val thatXCoef = that.getCoefficientByVar(x)
    
    assert(thisXCoef != 0 && thatXCoef != 0)

    val (newCoefs, newVars) = if (thatXCoef < 0 && thisXCoef > 0) {
      /* this is an upper bound; that is a lower bound */
      reorder(scale(thisCoefs, -1*thatXCoef)++scale(thatCoefs, thisXCoef), thisVars++thatVars)
    } else if (thisXCoef < 0 && thatXCoef > 0) {
      /* this is a lower bound; that is an upper bound */
      reorder(scale(thisCoefs, thatXCoef)++scale(thatCoefs, -1*thisXCoef), thisVars++thatVars)
    } else return None

    Some(GEQ(newCoefs, newVars))
  }

  def tightJoin(that: GEQ, x: String): Option[GEQ] = {
    assert(containsVar(x) && that.containsVar(x))
    assert(noZeroCoef && that.noZeroCoef)

    val (thisCoefs, thisVars) = this.removeVar(x)
    val (thatCoefs, thatVars) = that.removeVar(x)
    val thisXCoef = this.getCoefficientByVar(x)
    val thatXCoef = that.getCoefficientByVar(x)
    
    assert(thisXCoef != 0 && thatXCoef != 0)

    val m = (thisXCoef - 1) * (thatXCoef - 1)
    val (newCoefs, newVars) = if (thatXCoef < 0 && thisXCoef > 0) {
      /* this is a lower bound; that is an upper bound */
      reorder(m::scale(thisCoefs, -1*thatXCoef)++scale(thatCoefs, thisXCoef), const::thisVars++thatVars)
    } else if (thisXCoef < 0 && thatXCoef > 0) {
      /* this is an upper bound; that is a lower bound */
      reorder((-m)::scale(thisCoefs, thatXCoef)++scale(thatCoefs, -1*thisXCoef), const::thisVars++thatVars)
    } else return None
    
    Some(GEQ(newCoefs, newVars))
  }
}

object Problem {
  var varIdx = 0
  val greeks = List("α", "β", "γ", "δ", "ϵ", "ζ", "η", "θ", "ι", "κ", "λ", "μ",
                    "ν", "ξ", "ο", "π", "ρ", "σ", "τ", "υ", "ϕ", "χ", "ψ", "ω")

  def partition(cs: List[Constraint[_]]): (List[EQ], List[GEQ]) = {
    val (eqs, geqs) = cs.partition(_.isInstanceOf[EQ])
    (eqs.asInstanceOf[List[EQ]], geqs.asInstanceOf[List[GEQ]])
  }
}

case class Problem(cs: List[Constraint[_]]) {
  import Problem._

  def generateNewVar(): String = {
    val oldIdx = varIdx
    varIdx += 1
    greeks(oldIdx)
  }

  val (eqs, geqs) = partition(cs)

  def getEqs= eqs

  def getGeqs = geqs

  def hasEq = eqs.size != 0

  def getVars = cs.map(_.getVars).flatten.toSet.toList

  val numVars = cs.map(_.getVars).flatten.toList.size

  def hasMostOneVar = cs.map(_.getVars).flatten.toList.size <= 1

  def containsVar(x: String): Boolean = 
    cs.foldLeft(false)((acc, c) => acc || c.containsVar(x))

  override def toString(): String = { "{ " + cs.mkString("\n  ") + " }" }

  /* A constraint is normalized if all coefficients are integers, and the
   * greatest common divisor of the coefficients (not including a_0) is 1.
   */
  def normalize(): Option[Problem] = {
    val newCs: List[Constraint[_]] = for (c <- cs) yield 
      c.normalize match {
        case None => return None
        case Some(cn) => cn
      }
    Some(Problem(newCs))
  }
  
  /* Elminates the equalities in the problem, returns a new problem that
   * not contains equalities.
   */
  def elimEQs(): Problem = {
    def eliminate(eqs: List[EQ], geqs: List[GEQ]): List[GEQ] = {
      if (eqs.nonEmpty) {
        val eq = eqs.head

        println("current constraints:")
        for (eq <- (eqs++geqs)) { println(s"  $eq") }

        eq.getFirstAtomicVar match {
          case None =>
            val ((ak, xk), idx) = eq.minCoef
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

          case Some((x, idx)) =>
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
    Problem(eliminate(getEqs, getGeqs))
  }
  
  /* Returns None if found contradictions, 
   * Otherwise return a problem contains simpler/tigher constraints
   */
  def reduce(): Option[Problem] = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)
    assert(getGeqs.nonEmpty) //TODO: necessary?

    //Use Set to remove identical items
    val cons = mutable.Set[Constraint[_]]() 
    val junks = mutable.Set[Constraint[_]]()

    for (Seq(c1, c2) <- getGeqs.combinations(2)) { 
      if (c1.contraWith(c2)) {
        println(s"contra: $c1, $c2")
        return None
      }
      c1.subsume(c2) match {
        case Some(c) => 
          println(s"subsume: $c1, $c2 => $c")
          cons += c
          junks += (if (c == c1) c2 else c1)
        case None => c1.tighten(c2) match {
          case Some(c) => 
            println(s"tighten: $c1, $c2 => $c")
            cons += c
            junks += c1 += c2
          case None => cons += c1 += c2
        }
      }
    }

    println(s"constraints: $cons")
    println(s"junks: $junks")
    Some(Problem((cons -- junks).toList))
  }

  def allTrivial(): Boolean = cs.foldLeft(true)((b, c) => b && c.trivial)

  def hasIntSolutions(): Boolean = {
    //TODO: do we need to call normalize on every iteration?
    normalize match {
      case Some(p) if p.cs.isEmpty => true
      case Some(p) if p.hasMostOneVar => 
        if (p.numVars == 1) {
          println(s"only one variable left: ${p.getVars.head}")
          true
        } else {
          assert(p.cs.size == 1)
          p.allTrivial
        }
      case Some(p) if p.hasEq => p.elimEQs.hasIntSolutions
      case Some(p) => 
        p.reduce match {
          case Some(p) =>
            val realSet = p.realShadowSet
            val darkSet = p.darkShadowSet
            if (realSet == darkSet) { p.realShadow.hasIntSolutions }
            else if (!p.realShadow.hasIntSolutions) false
            else if (p.darkShadow.hasIntSolutions) true
            else {
              /* real shadow has int solution; but dark shadow does not */
              ???
              
            }
          case None => false
        }
      case None => false
    }
  }

  /* Split the inequalities list into two, the first list contains
   * variable x, while the second one not.
   */
  private def partitionGEQs(x: String): (List[GEQ], List[GEQ]) = {
    geqs.partition(_.containsVar(x))
  }

  /* We choose the variable that minimizes the number of constraints
   * resulting from the combination of upper and lower bounds, which
   * is the variable who has minimum frequency.
   */
  private def chooseVar(): String = {
    cs.map(_.getVars).flatten.groupBy(x=>x).toSeq.sortBy(_._2.length).head._1
  }

  /* Perform a classical Fourier-Motzkin variable elimination,
   * and obtain a new constraint set called real shadow.
   * See section 2.3.1 of paper The Omega Test in CACM.
   */
  def realShadow(): Problem = { Problem(realShadowSet.toList) }

  def realShadowSet(): mutable.Set[Constraint[_]] = {
    val x = chooseVar()
    println(s"real shadow chooses var: $x")
    realShadowSet(x)
  }
  
  def realShadowSet(x: String): mutable.Set[Constraint[_]] = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)
    
    val (ineqx, ineqnox) = partitionGEQs(x)
    val cons = mutable.Set[Constraint[_]]()
    cons ++= ineqnox

    for (Seq(ineq1, ineq2) <- ineqx.combinations(2)) {
      ineq1.join(ineq2, x) match {
        case Some(ineq) if ineq.trivial => /* trivially holds, no need to add to new constraints */
        case Some(ineq) => 
          println(s"real shadow eliminating $ineq1, $ineq2 => $ineq")
          cons += ineq
        case None => 
          /* In this case, ineq1 and ineq2 are not an upper/lower bound pair,
           * presumably should not happen since the reduce/subsume should 
           * be able to eliminate redundant constraints. 
           */
      }
    }

    assert(cons.size < getGeqs.size)
    cons
  }

  def chooseVarMinCoef(): String = {
    val (((c, x), _), _) = minWithIndex(cs.map(_.minCoef))(Ordering.by({ 
      case x: ((Int,String),Int) => abs(x._1._1) 
    }))
    x
  }

  def darkShadow(): Problem = { Problem(darkShadowSet.toList) }

  def darkShadowSet(): mutable.Set[Constraint[_]] = {
    var x = chooseVarMinCoef()
    println(s"dark shadow chooses var: $x")
    darkShadowSet(x)
  }
  
  /* Perform a variant Fourier-Motzkin variable elimination.
   */
  def darkShadowSet(x: String): mutable.Set[Constraint[_]] = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)

    val (ineqx, ineqnox) = partitionGEQs(x)
    val cons = mutable.Set[Constraint[_]]()
    cons ++= ineqnox
    
    for (Seq(ineq1, ineq2) <- ineqx.combinations(2)) {
      ineq1.tightJoin(ineq2, x) match {
        case Some(ineq) if ineq.trivial =>
        case Some(ineq) =>
          println(s"dark shadow eliminating $ineq1, $ineq2 => $ineq")
          cons += ineq
        case None =>
      }
    }
    
    assert(cons.size < getGeqs.size)
    cons
  }
  
  /* TODO: consider to remove this */
  def mergeTightIneqs(): Problem = {
    /* This phrase should after equality elimination */
    assert(getEqs.isEmpty)

    def merge(geqs: List[GEQ], acc: List[Constraint[_]]): List[Constraint[_]] = {
      if (geqs.isEmpty) acc
      else {
        val geq = geqs.head
        for ((other,idx) <- geqs.tail.zipWithIndex) {
          geq.tighten(other) match {
            case Some(c) => 
              println(s"tighten: $geq, $other => $c")
              //println(s"removed: ${removeByIdx(geqs.tail, idx)}")
              return merge(removeByIdx(geqs.tail, idx), c::acc)
            case None => 
          }
        }
        merge(geqs.tail, geqs.head::acc)
      }
    }

    Problem(merge(getGeqs, List()))
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
  //val p1elim = p1.elimEQs
  //println("after elimination: " + p1elim)

  ///////////////////////////////

  val eq3 = EQ(List(-17, 7, 12, 31), List(const, "x", "y", "z"))
  val eq4 = EQ(List(-7,  3, 5,  14), List(const, "x", "y", "z"))
  val p2 = Problem(List(eq3, eq4)).normalize.get
  println(p2)
  val p2elim = p2.elimEQs
  println(s"eq eliminated: $p2elim")
  
  val ineq1 = GEQ(List(-1, 1), List(const, "x"))
  val ineq2 = GEQ(List(40, -1), List(const, "x"))
  //println(ineq2.normalize.get)
  val ineq3 = GEQ(List(50, 1), List(const, "y"))
  val ineq4 = GEQ(List(50, -1), List(const, "y"))
  val p3 = Problem(List(eq3, eq4, ineq1, ineq2, ineq3, ineq4))
  println(p3)

  val p3elim = p3.elimEQs.normalize.get
  println(s"eq eliminated:\n $p3elim")
  val p3reduced = p3elim.reduce.get
  println(s"reduced:\n $p3reduced")
  
  val p3ans = p3.hasIntSolutions
  assert(p3ans)
  println(s"p3 has integer solutions: ${p3ans}")

  val ineq5 = GEQ(List(11, 13), List(const, "a")).normalize.get
  println(ineq5)
  val ineq6 = GEQ(List(28, -13), List(const, "a")).normalize.get
  println(ineq6)

  ///////////////////////////////

  val ineq7 = GEQ(List(-2, 3, 5), List(const, "x", "y"))
  val ineq8 = GEQ(List(0, -3,-5), List(const, "x", "y"))
  println(s"contraWith: ${ineq7.contraWith(ineq8)}") //true

  println(s"contraWith: ${GEQ(List(-5, 2, 3), List(const, "a", "b"))
              .contraWith(GEQ(List(-9, -2, -3), List(const, "a", "b")))}") //true

  println(s"contraWith: ${GEQ(List(9, 2, 3), List(const, "a", "b"))
              .contraWith(GEQ(List(-5, -2, -3), List(const, "a", "b")))}") //false

  println(s"contraWith: ${GEQ(List(0, 2, 3), List(const, "a", "b"))
              .contraWith(GEQ(List(2, -2, -3), List(const, "a", "b")))}") //false

  ///////////////////////////////

  println(s"can be merged: ${GEQ(List(-6, 2, 3), List(const, "a", "b"))
                      .tighten(GEQ(List(6, -2, -3), List(const, "a", "b")))}")

  val p4 = Problem(List(GEQ(List(-6, 2, 3), List(const, "a", "b")),
                        GEQ(List(6, -2, -3), List(const, "a", "b")),
                        GEQ(List(-5, 2, 3), List(const, "a", "c")),
                        GEQ(List(-10, 2, 3), List(const, "a", "c"))))
  println(p4)
  val p4reduced = p4.reduce.get
  println(p4reduced)

  println(s"num of vars: ${p4reduced.numVars}")

  ///////////////////////////////
  
  val ineq9 = GEQ(List(0, 3, 2), List(const, "x", "y"))
  val ineq10 = GEQ(List(5, -2, 4), List(const, "x", "y"))
  println(ineq9.join(ineq10, "x")) // 15 + 16y >= 0
  println(ineq10.join(ineq9, "x")) // 15 + 16y >= 0

  println(GEQ(List(-3, 1), List(const, "x")).join(GEQ(List(5, -1), List(const, "x")), "x")) // 2 >= 0
  println(GEQ(List(5, -1), List(const, "x")).join(GEQ(List(-3, 1), List(const, "x")), "x")) // 2 >= 0

  ///////////////////////////////
  
  val p5 = Problem(List(GEQ(List(7, -3, -2), List(const, "x", "y")),  // 7 - 3x - 2y >= 0
                        GEQ(List(15, -6, -4), List(const, "x", "y")), // 15 - 6x - 4y >= 0
                        GEQ(List(1, 1), List(const, "x")),            // 1 + x >= 0
                        GEQ(List(0, 2), List(const, "y"))))           // 0 + 2y >= 0

  println(s"p5 var with min ceof: ${p5.chooseVarMinCoef}") //x
  val p5ans = p5.hasIntSolutions
  assert(p5ans)
  println(s"p5 has integer solutions: ${p5ans}")

  val p6 = Problem(List(GEQ(List(4, -3, -2), List(const, "x", "y")),  // 4 - 3x - 2y >= 0
                        GEQ(List(-1, 1), List(const, "x")),           // -1 + x >= 0
                        GEQ(List(-1, 1), List(const, "y"))))          // -1 + y >= 0
  val p6ans = p6.hasIntSolutions
  assert(!p6ans)
  println(s"p6 has integer solutions: ${p6ans}")

  ///////////////////////////////

  println(GEQ(List(10, -1, 5), List(const, "x", "y"))
          .tightJoin(GEQ(List(-12, 1, 8), List(const, "x", "y")), "x"))
  println(GEQ(List(-12, 1, 8), List(const, "x", "y"))
          .tightJoin(GEQ(List(10, -1, 5), List(const, "x", "y")), "x"))
  
  val p7 = Problem(List(GEQ(List(10, -1, 5), List(const, "x", "y")),
                        GEQ(List(-12, 1, 8), List(const, "x", "y"))))

  assert(p7.realShadowSet("x") == p7.darkShadowSet("x"))
  println(p7.realShadowSet("x"))
  println(p7.darkShadowSet("x"))
}

