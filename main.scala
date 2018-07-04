
object Main extends App {
  if (args.length !=2) {
    println("Usage: scala MyProver '<formula1>' '<formula2>'")
    sys.exit(1)
  }
  var parser: Parser = null
  var leftTree: Node = null
  var rightTree: Node = null
  parser = new Parser(args(0))
  leftTree = parser.parseFormula()
  parser = new Parser(args(1))
  rightTree = parser.parseFormula()

  var prover: Prover = new Prover(List(leftTree), List(rightTree))
  if(prover.run) {
    println("provable")
  }
  else {
    println("not provable")
  }
}

/* === Prover === */
class Prover(var leftTrees: List[Node], var rightTrees: List[Node]) {
  /*
  A single step in the proof is represented as two lists of ASTs.
  The goal is to reduce ASTs into single variables, thus we have at the end two lists of variables.

  Each new step is made via a recursive call, this allows the proof to 'split' without any complication when needed.
   */
  var lhs: List[Node] = leftTrees
  var rhs: List[Node] = rightTrees

  def run: Boolean = {
    if (canBeReduced) {
      val newProvers: (Prover, Prover) = reduce
      if (newProvers._2 == null)
        return newProvers._1.run
      else if (newProvers._1 != null)
        return newProvers._1.run && newProvers._2.run // split here
    }
    evaluate
  }

  /**
    * Returns one or two provers representing the next step in the proof.
    */
  def reduce: (Prover, Prover) = {
    if (canBeReducedLeft) {
      for (ast <- lhs) {
        if (ast.isInstanceOf[OpNode]) {
          if (ast.asInstanceOf[OpNode].opType == OpType.AND) {
            return (reduceLeftAnd, null)
          }
          else if (ast.asInstanceOf[OpNode].opType == OpType.OR) {
            return reduceLeftOr
          }
          else if (ast.asInstanceOf[OpNode].opType == OpType.NOT) {
            return (reduceLeftNot, null)
          }
        }
      }
    }
    else if (canBeReducedRight) {
      for (ast <- rhs) {
        if (ast.isInstanceOf[OpNode]) {
          if (ast.asInstanceOf[OpNode].opType == OpType.AND) {
            return reduceRightAnd
          }
          else if (ast.asInstanceOf[OpNode].opType == OpType.OR) {
            return (reduceRightOr, null)
          }
          else if (ast.asInstanceOf[OpNode].opType == OpType.NOT) {
            return (reduceRightNot, null)
          }
        }
      }
    }
    return (null, null)
  }

  /**
    * Tells if lists are only variables or not.
    * @return true if they're only variables, false otherwise
    */
  def canBeReduced: Boolean = {
    canBeReducedLeft || canBeReducedRight
  }

  def canBeReducedLeft: Boolean = {
    for (tree <- lhs) {
      if (!tree.isInstanceOf[VariableNode])
        return true
    }
    false
  }

  def canBeReducedRight: Boolean = {
    for (tree <- rhs) {
      if (!tree.isInstanceOf[VariableNode])
        return true
    }
    false
  }

  /**
    * Evaluates when there's only variables if it matches id-opt or not.
    * @return true if match, false otherwise
    */
  def evaluate: Boolean = {
    if (canBeReduced)
      return false
    for (node <- lhs)  {
      if (node.isInstanceOf[VariableNode]) {
        for (node2 <- rhs) {
          if (node2.isInstanceOf[VariableNode]) {
            if (node.asInstanceOf[VariableNode].c == node2.asInstanceOf[VariableNode].c) {
              return true
            }
          }
        }
      }
    }
    false
  }

  def dump = {
    for(ast <- lhs) {
      ast.dump
      print(", ")
    }
    print(" |- ")
    for (ast <- rhs) {
      ast.dump
      print(", ")
    }
    println("")
  }

  /* Inference rules below : */
  def reduceRightNot: Prover = {
    val firstNot: OpNode = getFirstOfType(rhs, OpType.NOT)
    val newRhs: List[Node] = rhs.filter(_ != firstNot)
    val newLhs: List[Node] = lhs :+ firstNot.leftChild
    return new Prover(newLhs, newRhs)
  }
  def reduceLeftNot: Prover = {
    val firstNot: OpNode = getFirstOfType(lhs, OpType.NOT)
    val newLhs: List[Node] = lhs.filter(_ != firstNot)
    val newRhs: List[Node] = rhs :+ firstNot.leftChild
    return new Prover(newLhs, newRhs)
  }
  def reduceRightAnd: (Prover, Prover) = {
    val firstAnd: OpNode = getFirstOfType(rhs, OpType.AND)
    val newLhs: List[Node] = lhs
    val newRhs1: List[Node] = rhs.filter(_ != firstAnd) :+ firstAnd.leftChild
    val newRhs2: List[Node] = rhs.filter(_ != firstAnd) :+ firstAnd.rightChild
    return (new Prover(newLhs, newRhs1), new Prover(newLhs, newRhs2))
  }
  def reduceLeftAnd: Prover = {
    val firstAnd: OpNode = getFirstOfType(lhs, OpType.AND)
    val newLhs: List[Node] = lhs.filter(_ != firstAnd) :+ firstAnd.leftChild :+ firstAnd.rightChild
    return new Prover(newLhs, rhs)
  }
  def reduceRightOr: Prover = {
    val firstOr: OpNode = getFirstOfType(rhs, OpType.OR)
    val newRhs: List[Node] = rhs.filter(_ != firstOr) :+ firstOr.leftChild :+ firstOr.rightChild
    return new Prover(lhs, newRhs)
  }
  def reduceLeftOr: (Prover, Prover) = {
    val firstOr: OpNode = getFirstOfType(lhs, OpType.OR)
    val newLhs1: List[Node] = lhs.filter(_ != firstOr) :+ firstOr.leftChild
    val newLhs2: List[Node] = lhs.filter(_ != firstOr) :+ firstOr.rightChild
    return (new Prover(newLhs1, rhs), new Prover(newLhs2, rhs))
  }

  def getFirstOfType(nodes: List[Node], nodeType: OpType.OpType): OpNode = {
    for (node <- nodes) {
      if (node.isInstanceOf[OpNode]) {
        if (node.asInstanceOf[OpNode].opType == nodeType)
          return node.asInstanceOf[OpNode]
      }
    }
    null
  }
}

/* === AST === */
abstract class Node {
  def dump
}

class OpNode(var leftChild: Node, var rightChild: Node, var opType: OpType.OpType) extends Node {
  override def dump: Unit = {
    print("(")
    leftChild.dump
    print(opType)
    if (rightChild != null)
      rightChild.dump
    print(")")
  }
}

object OpType extends Enumeration {
  type OpType = Value
  val AND, OR, NOT = Value /* NOT nodes have only a leftChild, rightChild = null */
}

class VariableNode(var c: Char) extends Node {
  override def dump: Unit = print(c)
}

/* === Parser === */
class Parser(var input: String) {
  var index: Int = 0

  def parseFormula(): Node = {
    var res: Node = null
    do {
      var c = read
      if (c == '(') {
        eat(' ')
        val f = parseFormula()
        eat(' ')
        eat(')')
        res = f
      }
      else if (c == '!') {
        val f = parseFormula()
        res = new OpNode(f, null, OpType.NOT)
      }
      else if (c.isLetter && c.isUpper) {
        res = new VariableNode(c)
      }
      else if (c == ' ' && res != null) {
        c = read
        if (c == '&') {
          eat(' ')
          val f2 = parseFormula()
          res = new OpNode(res, f2, OpType.AND)
        }
        else if (c == '|') {
          eat(' ')
          val f2 = parseFormula()
          res = new OpNode(res, f2, OpType.OR)
        }
        else {
          throw new Exception("expected & or | but found: " + c)
        }
      }
      else {
        throw new Exception("expected ( or ! or a capital letter but found: " + c)
      }
    } while (hasNextOp)
    res
  }

  def eat(ref: Char) = {
    val c = read
    if (c != ref) {
      throw new Exception("Expected: " + ref + " but found: " + c)
    }
  }
  def read: Char = {
    if (!hasNext)
      throw new Exception("Unexpected end of file")
    val c = input.charAt(index)
    index += 1
    c
  }
  def hasNext: Boolean = {
    index < input.length
  }

  def getNext: Char = {
    input.charAt(index)
  }

  def hasNextOp: Boolean = {
    if (index < input.length - 1) {
      return input.charAt(index) == ' ' && (input.charAt(index + 1) == '|' || input.charAt(index + 1) == '&')
    }
    false
  }
}
