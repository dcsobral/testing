object RedBlackTest extends scala.collection.immutable.RedBlack[Int] {
  def isSmaller(x: Int, y: Int) = x < y
}

import RedBlackTest._

def computeDepth[B](t: Tree[B]) = Iterator.iterate(t) {
  case ne: NonEmpty[B] => ne.left
  case other => other
}.takeWhile(!_.isEmpty).filter(_.isBlack).size

def  findDepth[B](zipper: List[NonEmpty[B]], depth: Int): List[NonEmpty[B]] = 
zipper match {
  case (_: BlackTree[B]) :: tail =>
   if (depth == 1) zipper else findDepth(tail, depth - 1)
  case _ :: tail => findDepth(tail, depth)
  case Nil => error("Defect: unexpected empty zipper while computing range")
}

def unzip[B](zipper: List[NonEmpty[B]], leftMost: Boolean): List[NonEmpty[B]] = {
  val next = if (leftMost) zipper.head.left else zipper.head.right
  next match {
    case node: NonEmpty[B] => unzip(node :: zipper, leftMost)
    case Empty => zipper
  }
}

def unzipBoth[B](left: Tree[B],
              right: Tree[B],
              leftZipper: List[NonEmpty[B]],
              rightZipper: List[NonEmpty[B]]): 
             (List[NonEmpty[B]], Boolean, Boolean) = (left, right) match {
  case (l: BlackTree[B], r: BlackTree[B]) =>
    unzipBoth(l.right, r.left, l :: leftZipper, r :: rightZipper)
  case (l: RedTree[B], r: RedTree[B]) =>
    unzipBoth(l.right, r.left, l :: leftZipper, r :: rightZipper)
  case (_, r: RedTree[B]) =>
    unzipBoth(left, r.left, leftZipper, r :: rightZipper)
  case (l: RedTree[B], _) =>
    unzipBoth(l.right, right, l :: leftZipper, rightZipper)
  case (Empty, Empty) =>
    (Nil, true, false)
  case (Empty, r: BlackTree[B]) =>
    val leftMost = true
    (unzip(r :: rightZipper, leftMost), false, leftMost)
  case (l: BlackTree[B], Empty) =>
    val leftMost = false
    (unzip(l :: leftZipper, leftMost), false, leftMost)
}

def compareDepth[B](left: Tree[B], right: Tree[B]): (List[NonEmpty[B]], Boolean, Boolean) = {
  unzipBoth(left, right, Nil, Nil)
}
      
def balance[B](x: Int, xv: B, tl: Tree[B], tr: Tree[B]) = (tl, tr) match {
  case (RedTree(y, yv, a, b), RedTree(z, zv, c, d)) =>
    RedTree(x, xv, BlackTree(y, yv, a, b), BlackTree(z, zv, c, d))
  case (RedTree(y, yv, RedTree(z, zv, a, b), c), d) =>
    RedTree(y, yv, BlackTree(z, zv, a, b), BlackTree(x, xv, c, d))
  case (RedTree(y, yv, a, RedTree(z, zv, b, c)), d) =>
    RedTree(z, zv, BlackTree(y, yv, a, b), BlackTree(x, xv, c, d))
  case (a, RedTree(y, yv, b, RedTree(z, zv, c, d))) =>
    RedTree(y, yv, BlackTree(x, xv, a, b), BlackTree(z, zv, c, d))
  case (a, RedTree(y, yv, RedTree(z, zv, b, c), d)) =>
    RedTree(z, zv, BlackTree(x, xv, a, b), BlackTree(y, yv, c, d))
  case (a, b) => 
    BlackTree(x, xv, a, b)
}
    
def subl[B](t: Tree[B]) = t match {
  case BlackTree(x, xv, a, b) => RedTree(x, xv, a, b)
  case _ => error("Defect: invariance violation; expected black, got "+t)
}
    
def balLeft[B](x: Int, xv: B, tl: Tree[B], tr: Tree[B]) = (tl, tr) match {
  case (RedTree(y, yv, a, b), c) => 
    RedTree(x, xv, BlackTree(y, yv, a, b), c)
  case (bl, BlackTree(y, yv, a, b)) => 
    balance(x, xv, bl, RedTree(y, yv, a, b))
  case (bl, RedTree(y, yv, BlackTree(z, zv, a, b), c)) => 
    RedTree(z, zv, BlackTree(x, xv, bl, a), balance(y, yv, b, subl(c)))
  case _ => error("Defect: invariance violation at "+tr)
}
    
def balRight[B](x: Int, xv: B, tl: Tree[B], tr: Tree[B]) = (tl, tr) match {
  case (a, RedTree(y, yv, b, c)) =>
    RedTree(x, xv, a, BlackTree(y, yv, b, c))
  case (BlackTree(y, yv, a, b), bl) =>
    balance(x, xv, RedTree(y, yv, a, b), bl)
  case (RedTree(y, yv, a, BlackTree(z, zv, b, c)), bl) =>
    RedTree(z, zv, balance(y, yv, subl(a), b), BlackTree(x, xv, c, bl))
  case _ => error("Defect: invariance violation at "+tl)
}
    
def append[B](tl: Tree[B], tr: Tree[B]): Tree[B] = (tl, tr) match {
  case (Empty, t) => t
  case (t, Empty) => t
  case (RedTree(x, xv, a, b), RedTree(y, yv, c, d)) =>
    append(b, c) match {
      case RedTree(z, zv, bb, cc) => RedTree(z, zv, RedTree(x, xv, a, bb), RedTree(y, yv, cc, d))
      case bc => RedTree(x, xv, a, RedTree(y, yv, bc, d))
    }
  case (BlackTree(x, xv, a, b), BlackTree(y, yv, c, d)) =>
    append(b, c) match {
      case RedTree(z, zv, bb, cc) => RedTree(z, zv, BlackTree(x, xv, a, bb), BlackTree(y, yv, cc, d))
      case bc => balLeft(x, xv, a, BlackTree(y, yv, bc, d))
    }
  case (a, RedTree(x, xv, b, c)) => RedTree(x, xv, append(a, b), c)
  case (RedTree(x, xv, a, b), c) => RedTree(x, xv, a, append(b, c))
}
      

