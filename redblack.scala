import org.scalacheck._
import Prop._
import Gen._

/*
Properties of a Red & Black Tree:

A node is either red or black.
The root is black. (This rule is used in some definitions and not others. Since the
root can always be changed from red to black but not necessarily vice-versa this 
rule has little effect on analysis.)
All leaves are black.
Both children of every red node are black.
Every simple path from a given node to any of its descendant leaves contains the same number of black nodes.
*/

abstract class RedBlackTest extends Properties("RedBlack") {
  object RedBlackTest extends scala.collection.immutable.RedBlack[String] {
    def isSmaller(x: String, y: String) = x < y
  }
  
  import RedBlackTest._
  
  def mkTree(level: Int, parentIsBlack: Boolean = false, label: String = ""): Gen[Tree[Unit]] = 
    if (level == 0) {
      value(Empty)
    } else {
      for {
        oddOrEven <- choose(0, 2)
        tryRed = oddOrEven.sample.get % 2 == 0 // work around arbitrary[Boolean] bug
        isRed = parentIsBlack && tryRed
        nextLevel = if (isRed) level else level - 1
        left <- mkTree(nextLevel, !isRed, label + "L")
        right <- mkTree(nextLevel, !isRed, label + "R")
      } yield {
        if (isRed) 
          RedTree(label + "N Red", (), left, right)
        else
          BlackTree(label + "N Black", (), left, right)
      }
    }

  def genTree = for {
    depth <- choose(0, 9)
    tree <- mkTree(depth)
  } yield tree
  
  type DestType = Unit
  type ModifyParm = Int
  def genParm(tree: Tree[Unit]): Gen[ModifyParm]
  def modify(tree: Tree[Unit], parm: ModifyParm): Tree[DestType]
  def genInput: Gen[(Tree[Unit], ModifyParm, Tree[DestType])] = for {
    tree <- genTree
    parm <- genParm(tree)
  } yield (tree, parm, modify(tree, parm))
  
  def rootIsBlack[A](t: Tree[A]) = t.isBlack
  
  def areAllLeavesBlack[A](t: Tree[A]): Boolean = t match {
    case Empty => t.isBlack
    case ne: NonEmpty[_] => List(ne.left, ne.right) forall areAllLeavesBlack
  }
  
  def areRedNodeChildrenBlack[A](t: Tree[A]): Boolean = t match {
    case RedTree(_, _, left, right) => List(left, right) forall (t => t.isBlack && areRedNodeChildrenBlack(t)) 
    case BlackTree(_, _, left, right) => List(left, right) forall areRedNodeChildrenBlack
    case Empty => true
  }
  
  def blackNodesToLeaves[A](t: Tree[A]): List[Int] = t match {
    case Empty => List(1)
    case BlackTree(_, _, left, right) => List(left, right) flatMap blackNodesToLeaves map (_ + 1)
    case RedTree(_, _, left, right) => List(left, right) flatMap blackNodesToLeaves
  }
  
  def areBlackNodesToLeavesEqual[A](t: Tree[A]): Boolean = t match {
    case Empty => true
    case ne: NonEmpty[_] => 
      (
        blackNodesToLeaves(ne).distinct.size == 1 
        && areBlackNodesToLeavesEqual(ne.left) 
        && areBlackNodesToLeavesEqual(ne.right)
      )
  }
  
  def orderIsPreserved[A](t: Tree[A]): Boolean = 
    t.iterator zip t.iterator.drop(1) forall { case (x, y) => isSmaller(x._1, y._1) }
    
  def setup(invariant: Tree[DestType] => Boolean) = forAll(genInput) { case (tree, parm, newTree) =>
    invariant(newTree)
  }

  property("root is black") = setup(rootIsBlack)
  property("all leaves are black") = setup(areAllLeavesBlack)
  property("children of red nodes are black") = setup(areRedNodeChildrenBlack)
  property("All descendant paths contains the same number of black nodes") = setup(areBlackNodesToLeavesEqual)
  property("Ordering of keys is preserved") = setup(orderIsPreserved)
}

object TestInsertion extends RedBlackTest {
  import RedBlackTest._
  
  override def genParm(tree: Tree[Unit]): Gen[ModifyParm] = choose(0, tree.iterator.size + 1)
  override def modify(tree: Tree[Unit], parm: ModifyParm): Tree[DestType] = tree update (generateKey(tree, parm), ())

  def generateKey(tree: Tree[Unit], parm: ModifyParm) = if (tree.iterator.size == parm) {
    tree.iterator.toList.map(_._1).apply(parm - 1).init.mkString + "RN"
  } else {
    tree.iterator.toList.map(_._1).apply(parm).init.mkString + "MN"
  }

  property("update adds elements") = forAll(genInput) { case (tree, parm, newTree) =>
    (newTree lookup generateKey(tree, parm)) != Empty
  }
}

object TestDeletion extends RedBlackTest {
  import RedBlackTest._
  override val seqType = Gen.frequency(
    (2, listFewRepetitions _),
    (3, listManyRepetitions _),
    (1, listEvenRepetitions _)
  )
  
  property("delete removes elements") = forAll(myGen(50)) { l =>
    val tree = l.foldLeft(Empty: Tree[Unit])((acc, n) => acc update (n, ()))
    forAll(Gen.choose(1, l.size)) { numberOfElementsToRemove =>
      forAll(Gen.pick(numberOfElementsToRemove, l)) { elementsToRemove =>
        val newTree = elementsToRemove.foldLeft(tree)((acc, n) => acc delete n)
        (elementsToRemove forall (n => newTree lookup n isEmpty)) :| "Tree: "+tree+"New Tree: "+newTree+" Elements to Remove: "+elementsToRemove 
      }
    }
  }
  
  override def setup(l: List[Int], invariant: Tree[Unit] => Boolean) = l.foldLeft((true, Empty: Tree[Unit])) { 
    case ((true, acc), n) => 
      val newRoot = if (acc lookup n isEmpty) acc update (n, ()) else acc delete n
      (invariant(newRoot), newRoot)
    case (failed, _) => failed
  }
}

object TestRange extends RedBlackTest {
  import RedBlackTest._
  override val seqType = Gen.frequency(
    (2, listFewRepetitions _),
    (3, listManyRepetitions _),
    (1, listEvenRepetitions _)
  )
  
  override def setup(l: List[Int], invariant: Tree[Unit] => Boolean) = {
    val (from, to, rest) = l.size match {
      case 0 => (None, None, Nil)
      case 1 => (Some(l.head), None, Nil)
      case _ => val f :: t :: r = l; (Some(f), Some(t), r)
    }
    val (flag, tree) = rest.foldLeft((true, Empty: Tree[Unit])) { 
      case ((true, acc), n) => 
        val newRoot = if (acc lookup n isEmpty) acc update (n, ()) else acc delete n
        (invariant(newRoot range (from, to)), newRoot)
      case (failed, _) => failed
    }
    (flag && invariant(tree range (from, to)), tree)
  }
}

object Test extends Properties("RedBlack") {
  include(TestInsertion)
  include(TestDeletion)
  include(TestRange)
}

