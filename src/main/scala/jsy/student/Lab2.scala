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
      case S(s) => try s.toDouble catch {case _ : Throwable => Double.NaN}
      case Undefined => Double.NaN
      case _ => throw new UnsupportedOperationException
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case S(s) => if (s == "") false else true
      case N(n) => if (n.isNaN) false else if (n == 0) false else true
      case Undefined => false
      case _ => throw new UnsupportedOperationException
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString //from prettyNumber in ast.scala
      case B(b) => if (b) "true" else "false"
      case _ => throw new UnsupportedOperationException
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
        //If we reach a value, simply return that value.
      case N(_) | B(_) | S(_) | Undefined => e

      case Var(x) => lookup(env,x)

      /* Inductive Cases */
        //Set variable to e1, extend env to include new variable, evaluate e2
      case ConstDecl(x,e1,e2) => {
        val v = eval(env, e1)
        val env2 = extend(env, x, v)
        eval(env2, e2)
      }

        //Neg and Not are fairly simple. Eval the inner expression,
        //then convert it to a number/boolean, then neg/not and return
        //an expression.
      case Unary(uop, e1) =>
        uop match {
        case Neg => N(-toNumber(eval(env, e1)))
        case Not => B(!toBoolean(eval(env,e1)))
        case _ => throw new UnsupportedOperationException
      }

      case Binary(bop,e1,e2) =>
        bop match {
            //Arithmatic Operators.
            //Plus. Strings append each other.
          case Plus =>
            (eval(env,e1), eval(env,e2)) match {
              case (S(e1), S(e2)) => S(e1 + e2)
              case (S(e1), e2) => S(e1 + toStr(eval(env,e2)))
              case (e1, S(e2)) => S(toStr(eval(env,e1)) + e2)
              //case (e1, e2) => eval(env,e1) + eval(env,e2)
              case _ => N(toNumber(eval(env, e1)) + toNumber(eval(env,e2)))
            }

            //Minus. Strings result in NaN
          case Minus =>
              N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))

            //Times. Strings result in NaN
          case Times =>
              N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))

            //Divide. Strings result in NaN
          case Div =>
              N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))


            //Equal
          case Eq =>
            if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(true)
              else B(false)


            //Not equal.
          case Ne =>
              if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(false)
              else B(true)


            //Less than
          case Lt =>
              if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(false)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(false)
              else B(true)


            //Less than or Equal to
          case Le =>
              if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(true)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(false)
              else B(true)


            //Greater than
          case Gt =>
              if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(false)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(true)
              else B(false)

            //Greater than or equal to
          case Ge =>
            if (N(toNumber(eval(env,e1))) == N(toNumber(eval(env,e2))))
                B(true)
              else if (toNumber(eval(env,e1)) > toNumber(eval(env,e2)))
                B(true)
              else B(false)

            //Logical AND. "Returns expr1 if it can be converted to false; otherwise, returns expr2.
          // Thus, when used with Boolean values, && returns true if both operands are true; otherwise, returns false."
          case And =>
              if (toBoolean(eval(env,e1))) eval(env,e2) else eval(env,e1)

            //Logical OR. "Returns expr1 if it can be converted to true; otherwise, returns expr2.
          // Thus, when used with Boolean values, || returns true if either operand is true."
          case Or =>
            if (toBoolean(eval(env,e1))) eval(env,e1) else eval(env,e2)

          case Seq => eval(env,e1);eval(env,e2)
        }
        //End BOps

        //Ternary operator. If X, then y, else z.
      case If(e1,e2,e3) =>
        if (toBoolean(eval(env,e1))) eval(env,e2) else eval(env,e3)


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
