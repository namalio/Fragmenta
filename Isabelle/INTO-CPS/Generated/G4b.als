module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig u, y1, y2, x, y, z extends Port  {
}

 fact {
   u.tgt = y2
   y1.tgt = z
   y2.tgt = x
   x.tgt = y
   y.tgt = u
   no z.tgt
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 6