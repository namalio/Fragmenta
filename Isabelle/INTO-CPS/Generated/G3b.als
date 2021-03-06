module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig y1, y2, x, y, s, x1, x2, y3, x0 extends Port  {
}

 fact {
   y1.tgt = x
   y2.tgt = s + x2
   x.tgt = y
   y.tgt = x1
   s.tgt = y
   x1.tgt = y3
   no x2.tgt
   y3.tgt = x0
   x0.tgt = y1
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 9