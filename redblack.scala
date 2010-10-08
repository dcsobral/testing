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
  
  def nodeAt[A](tree: Tree[A], n: Int): Option[(String, A)] = if (n < tree.iterator.size && n >= 0)
    Some(tree.iterator.drop(n).next)
  else
    None
    
  def treeContains[A](tree: Tree[A], key: String) = tree.iterator.map(_._1) contains key
  
  def mkTree(level: Int, parentIsBlack: Boolean = false, label: String = ""): Gen[Tree[Int]] = 
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
          RedTree(label + "N Red", 0, left, right)
        else
          BlackTree(label + "N Black", 0, left, right)
      }
    }

  def minimumSize = 0
  def maximumSize = 8
  def genTree = for {
    depth <- choose(minimumSize, maximumSize + 1)
    tree <- mkTree(depth)
  } yield tree
  
  type ModifyParm = Int
  def genParm(tree: Tree[Int]): Gen[ModifyParm]
  def modify(tree: Tree[Int], parm: ModifyParm): Tree[Int]
  
  def genInput: Gen[(Tree[Int], ModifyParm, Tree[Int])] = for {
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
    
  def setup(invariant: Tree[Int] => Boolean) = forAll(genInput) { case (tree, parm, newTree) =>
    invariant(newTree)
  }

  property("root is black") = setup(rootIsBlack)
  property("all leaves are black") = setup(areAllLeavesBlack)
  property("children of red nodes are black") = setup(areRedNodeChildrenBlack)
  property("All descendant paths contains the same number of black nodes") = setup(areBlackNodesToLeavesEqual)
  property("Ordering of keys is preserved") = setup(orderIsPreserved)
}

object TestInsert extends RedBlackTest {
  import RedBlackTest._
  
  override def genParm(tree: Tree[Int]): Gen[ModifyParm] = choose(0, tree.iterator.size + 1)
  override def modify(tree: Tree[Int], parm: ModifyParm): Tree[Int] = tree update (generateKey(tree, parm), 0)

  def generateKey(tree: Tree[Int], parm: ModifyParm): String = nodeAt(tree, parm) match {
    case Some((key, _)) => key.init.mkString + "MN"
    case None => nodeAt(tree, parm - 1) match {
      case Some((key, _)) => key.init.mkString + "RN"
      case None  => "N"
    }
  }

  property("update adds elements") = forAll(genInput) { case (tree, parm, newTree) =>
    treeContains(newTree, generateKey(tree, parm))
  }
}

object TestModify extends RedBlackTest {
  import RedBlackTest._
  
  def newValue = 1
  override def minimumSize = 1
  override def genParm(tree: Tree[Int]): Gen[ModifyParm] = choose(0, tree.iterator.size)
  override def modify(tree: Tree[Int], parm: ModifyParm): Tree[Int] = nodeAt(tree, parm) map { 
    case (key, _) => tree update (key, newValue)
  } getOrElse tree

  property("update modifies values") = forAll(genInput) { case (tree, parm, newTree) =>
    nodeAt(tree,parm) forall { case (key, _) =>
      newTree.iterator contains (key, newValue)
    }
  }
}

object TestDeletion extends RedBlackTest {
  import RedBlackTest._

  override def minimumSize = 1
  override def genParm(tree: Tree[Int]): Gen[ModifyParm] = choose(0, tree.iterator.size)
  override def modify(tree: Tree[Int], parm: ModifyParm): Tree[Int] = nodeAt(tree, parm) map { 
    case (key, _) => tree delete key
  } getOrElse tree
  
  property("delete removes elements") = forAll(genInput) { case (tree, parm, newTree) =>
    treeContains(newTree

    forAll(myGen(50)) { l =>
    val tree = l.foldLeft(Empty: Tree[Int])((acc, n) => acc update (n, ()))
    forAll(Gen.choose(1, l.size)) { numberOfElementsToRemove =>
      forAll(Gen.pick(numberOfElementsToRemove, l)) { elementsToRemove =>
        val newTree = elementsToRemove.foldLeft(tree)((acc, n) => acc delete n)
        (elementsToRemove forall (n => newTree lookup n isEmpty)) :| "Tree: "+tree+"New Tree: "+newTree+" Elements to Remove: "+elementsToRemove 
      }
    }
  }
}

object TestRange extends RedBlackTest {
  import RedBlackTest._
  override val seqType = Gen.frequency(
    (2, listFewRepetitions _),
    (3, listManyRepetitions _),
    (1, listEvenRepetitions _)
  )
  
  override def setup(l: List[Int], invariant: Tree[Int] => Boolean) = {
    val (from, to, rest) = l.size match {
      case 0 => (None, None, Nil)
      case 1 => (Some(l.head), None, Nil)
      case _ => val f :: t :: r = l; (Some(f), Some(t), r)
    }
    val (flag, tree) = rest.foldLeft((true, Empty: Tree[Int])) { 
      case ((true, acc), n) => 
        val newRoot = if (acc lookup n isEmpty) acc update (n, ()) else acc delete n
        (invariant(newRoot range (from, to)), newRoot)
      case (failed, _) => failed
    }
    (flag && invariant(tree range (from, to)), tree)
  }
}

object Test extends Properties("RedBlack") {
  include(TestInsert)
  include(TestModify)
  include(TestDelete)
  include(TestRange)
}

