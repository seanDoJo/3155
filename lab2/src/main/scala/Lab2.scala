object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if(n.isNaN) Double.NaN else n
      case Undefined => Double.NaN
      case B(b) => if(b) 1 else 0
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN}
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if(n.isNaN){
	      	false
	      }
	      else if (n != 0) {
	      	true
	      }
	      else {
	      	false
	      }
      case S(s) => if(s == "") false else true
      case Undefined => false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => if(b) "true" else "false"
      case N(n) => {
      	if(!(n.isWhole())) n.toString else f"$n%.0f"
      } 
      case Undefined => "undefined"
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)

    e match {
      /* Base Cases */
      case N(n) => N(n)
      case B(b) => B(b)
      case S(s) => S(s)
      case Var(x) => get(env, x)
      case Undefined => Undefined
      /* Inductive Cases */
      case Unary(uop, e1) => uop match {
      	case Neg => N(-1 * toNumber(eval(env, e1)))
      	case Not => B(!(toBoolean(eval(env, e1))))
      }
      
      case Binary(bop, e1, e2) => bop match {
      	case Or => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case N(n) => if(n == 0) res2 else N(n)
      			case B(b) => if(!b) res2 else B(b)
      			case S(s) => if(s == "") res2 else S(s)
      			case _ => B(false)
      		}
      	}

      	case And => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case N(n) => if(n == 0) N(n) else res2
      			case B(b) => if(!b) B(b) else res2
      			case S(s) => if(s == "") S(s) else res2
      			case _ => B(false)
      		}
      	}

      	case Plus => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => S(s + toStr(res2))
      			case _ => res2 match {
      				case S(s) => S(toStr(res1) + s)
      				case _ => N(toNumber(res1) + toNumber(res2))
      			}
      		}
      	}

      	case Minus => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => {
      				val med1 = toNumber(res1)
      				if (med1 == Double.NaN){
      					N(med1)
      				}
   						else {
   							val med2 = toNumber(res2)
   							if (med2 == Double.NaN) {
   								N(med2)
   							}
   							else {
   								N(med1 - med2)
   							}
   						}
      			}
      			case _ => res2 match {
      				case S(s) => {
      					val med2 = toNumber(res2)
   							if (med2 == Double.NaN) {
   								N(med2)
   							}
   							else {
   								N(toNumber(res1) - med2)
   							}
      				}
      				case _ => N(toNumber(res1) - toNumber(res2))
      			}
      		}
      	}

      	case Times => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => {
      				val med1 = toNumber(res1)
      				if (med1 == Double.NaN){
      					N(med1)
      				}
   						else {
   							val med2 = toNumber(res2)
   							if (med2 == Double.NaN) {
   								N(med2)
   							}
   							else {
   								N(med1 * med2)
   							}
   						}
      			}
      			case _ => res2 match {
      				case S(s) => {
      					val med2 = toNumber(res2)
   							if (med2 == Double.NaN) {
   								N(med2)
   							}
   							else {
   								N(toNumber(res1) * med2)
   							}
      				}
      				case _ => N(toNumber(res1) * toNumber(res2))
      			}
      		}
      	}

      	case Div => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => {
      				val med1 = toNumber(res1)
      				if (med1 == Double.NaN){
      					N(med1)
      				}
   						else {
   							val med2 = toNumber(res2)
   							if (med2 == Double.NaN) {
   								N(med2)
   							}
   							else {
   								N(med1 / med2)
   							}
   						}
      			}
      			case _ => res2 match {
      				case S(s) => {
      					val med2 = toNumber(res2)
   							if (med2 == Double.NaN) {
   								N(med2)
   							}
   							else {
   								N(toNumber(res1) / med2)
   							}
      				}
      				case _ => N(toNumber(res1) / toNumber(res2))
      			}
      		}
      	}

      	case Eq => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => res2 match {
      				case S(x) => B(toStr(res1) == toStr(res2))
      				case N(y) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) == toNumber(res2))
      				}
      				case B(z) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) == toNumber(res2))
      				}
      				case _ => B(false)
      			}
      			case N(n) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) == toNumber(res2))
      				}
      				case N(y) => B(toNumber(res1) == toNumber(res2))
      				case B(z) => B(toNumber(res1) == toNumber(res2))
      				case _ => B(false)
      			}
      			case B(b) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) == toNumber(res2))
      				}
      				case N(y) => B(toNumber(res1) == toNumber(res2))
      				case B(z) => B(toBoolean(res1) == toBoolean(res2))
      				case _ => B(false)
      			}
      			case _ => B(false)
      		}
      	}

      	case Ne => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => res2 match {
      				case S(x) => B(toStr(res1) != toStr(res2))
      				case N(y) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(true) else B(toNumber(res1) != toNumber(res2))
      				}
      				case B(z) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(true) else B(toNumber(res1) != toNumber(res2))
      				}
      				case _ => B(true)
      			}
      			case N(n) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(true) else B(toNumber(res1) != toNumber(res2))
      				}
      				case N(y) => B(toNumber(res1) != toNumber(res2))
      				case B(z) => B(toNumber(res1) != toNumber(res2))
      				case _ => B(true)
      			}
      			case B(b) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(true) else B(toNumber(res1) != toNumber(res2))
      				}
      				case N(y) => B(toNumber(res1) != toNumber(res2))
      				case B(z) => B(toBoolean(res1) != toBoolean(res2))
      				case _ => B(true)
      			}
      			case _ => B(true)
      		}
      	}

      	case Lt => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => res2 match {
      				case S(x) => B(toStr(res1) < toStr(res2))
      				case N(n) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med < toNumber(res2))
      				}
      				case B(b) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med < toNumber(res2))
      				}
      				case _ => B(false)
      			}
      			case N(n) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) < toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) < toNumber(res2))
      				case B(b) => B(toNumber(res1) < toNumber(res2))
      				case _ => B(false)
      			}
      			case B(b) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) < toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) < toNumber(res2))
      				case B(b) => B(toBoolean(res1) < toBoolean(res2))
      				case _ => B(false)
      			}
      			case Undefined => B(false)
      			case _ => B(false)
      		}
      	}

      	case Le => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => res2 match {
      				case S(x) => B(toStr(res1) <= toStr(res2))
      				case N(n) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med <= toNumber(res2))
      				}
      				case B(b) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med <= toNumber(res2))
      				}
      				case _ => B(false)
      			}
      			case N(n) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) <= toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) <= toNumber(res2))
      				case B(b) => B(toNumber(res1) <= toNumber(res2))
      				case _ => B(false)
      			}
      			case B(b) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) <= toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) <= toNumber(res2))
      				case B(b) => B(toBoolean(res1) <= toBoolean(res2))
      				case _ => B(false)
      			}
      			case Undefined => B(false)
      			case _ => B(false)
      		}
      	}

      	case Gt => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => res2 match {
      				case S(x) => B(toStr(res1) > toStr(res2))
      				case N(n) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med > toNumber(res2))
      				}
      				case B(b) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med > toNumber(res2))
      				}
      				case _ => B(false)
      			}
      			case N(n) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) > toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) > toNumber(res2))
      				case B(b) => B(toNumber(res1) > toNumber(res2))
      				case _ => B(false)
      			}
      			case B(b) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) > toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) > toNumber(res2))
      				case B(b) => B(toBoolean(res1) > toBoolean(res2))
      				case _ => B(false)
      			}
      			case Undefined => B(false)
      			case _ => B(false)
      		}
      	}

      	case Ge => {
      		val res1 = eval(env, e1)
      		val res2 = eval(env, e2)
      		res1 match {
      			case S(s) => res2 match {
      				case S(x) => B(toStr(res1) >= toStr(res2))
      				case N(n) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med >= toNumber(res2))
      				}
      				case B(b) => {
      					val med = toNumber(res1)
      					if (med == Double.NaN) B(false) else B(med >= toNumber(res2))
      				}
      				case _ => B(false)
      			}
      			case N(n) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) >= toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) >= toNumber(res2))
      				case B(b) => B(toNumber(res1) >= toNumber(res2))
      				case _ => B(false)
      			}
      			case B(b) => res2 match {
      				case S(x) => {
      					val med = toNumber(res2)
      					if (med == Double.NaN) B(false) else B(toNumber(res1) >= toNumber(res2))
      				}
      				case N(n) => B(toNumber(res1) >= toNumber(res2))
      				case B(b) => B(toBoolean(res1) >= toBoolean(res2))
      				case _ => B(false)
      			}
      			case Undefined => B(false)
      			case _ => B(false)
      		}
      	}

      	case Seq => {
      		eval(env, e1)
      		eval(env, e2)
      	}
      }

      case If(e1, e2, e3) => {
      	val res1 = toBoolean(eval(env, e1))
      	val res2 = eval(env, e2)
      	val res3 = eval(env, e3)
				if(res1) res2 else res3
      }

      case ConstDecl(x, e1, e2) => {
      	val env2 = extend(env, x, eToVal(e1))
      	eval(env2, e2)
      }

      case Print(e1) => println(pretty(eToVal(e1))); Undefined
    }
  }
    
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

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