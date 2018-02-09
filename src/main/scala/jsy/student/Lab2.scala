package jsy.student

import jsy.lab2.Lab2Like

object Lab2 extends jsy.util.JsyApplication with Lab2Like {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * Kyle Gronberg
   * 
   * Partner: Ben Shoeman
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with  your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */



  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   *
   * You can catch an exception in Scala using:
   * try ... catch { case ... => ... }
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) 1.0 else 0.0
      case S(s) => s.toDouble
      case Undefined => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case S(s) => if (s == "") false else true
      case N(n) => if (n.isNaN) false else if (n == 0) false else true
      case Undefined => false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString //from prettyNumber in ast.scala
      case B(b) => if (b) "true" else "false"
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined => e

      case Unary(uop, e1) =>
        uop match {
        case Neg => N(-toNumber(eval(env, e1)))
        case Not => B(!toBoolean(eval(env,e1)))
      }

      case Binary(bop,e1,e2) =>
        bop match {
          case Plus =>
            (eval(env,e1), eval(env,e2)) match {
              case (S(e1), S(e2)) => S(e1 + e2)
              case (S(e1), e2) => S(e1 + toStr(eval(env,e2)))
              case (e1, S(e2)) => S(toStr(eval(env,e1)) + e2)
              case (e1, e2) => eval(env,e1) + eval(env,e2)
              case _ => N(toNumber(eval(env, e1)) + toNumber(eval(env,e2)))
            }
          case Minus =>
            (eval(env,e1), eval(env,e2)) match {
              case (S(e1), S(e2)) => N(Double.NaN)
              case (e1, S(e2)) => N(Double.NaN)
              case (S(e1), e2) => N(Double.NaN)
              case _ => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
            }
          case Times =>
            (eval(env,e1), eval(env,e2)) match {
              case (S(e1), S(e2)) => N(Double.NaN)
              case (e1, S(e2)) => N(Double.NaN)
              case (S(e1), e2) => N(Double.NaN)
              case _ => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
            }
          case Div =>
            (eval(env,e1), eval(env,e2)) match {
              case (S(e1), S(e2)) => N(Double.NaN)
              case (e1, S(e2)) => N(Double.NaN)
              case (S(e1), e2) => N(Double.NaN)
              case _ => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
          }
          case Eq =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(true)
              else B(false)
            }
          case Ne =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(false)
              else B(true)
            }
          case Lt =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(false)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(false)
              else B(true)
            }
          case Le =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(true)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(false)
              else B(true)
            }
          case Gt =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(false)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(true)
              else B(false)
            }
          case Ge =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(true)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(true)
              else B(false)
            }
          case And =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (toBoolean(eval(env,e1))) eval(env,e2) else eval(env,e1)
            }
          case Or =>
            (eval(env,e1), eval(env,e2)) match {
              case _ => if (toBoolean(eval(env,e1))) eval(env,e1) else eval(env,e2)
            }
          case Seq => eval(env,e1);eval(env,e2)
        }
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case _ => Undefined
    }
  }



  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
