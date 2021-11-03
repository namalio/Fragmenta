module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig a, b1, b3, b2, b4, c1, c3, c2, d1, d2 extends Port  {
}

 fact {
   a.tgt = b1
   b1.tgt = b4
   b3.tgt = b2
   b2.tgt = c1
   b4.tgt = c3
   no c1.tgt
   c3.tgt = c2
   c2.tgt = d1
   d1.tgt = d2
   d2.tgt = b3
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 10