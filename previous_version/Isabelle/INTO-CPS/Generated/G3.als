module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig y1, y2, x, y, s, x1, x2 extends Port  {
}

 fact {
   y1.tgt = x
   y2.tgt = s + x2
   x.tgt = y
   y.tgt = x1
   s.tgt = y
   no x1.tgt
   no x2.tgt
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 7