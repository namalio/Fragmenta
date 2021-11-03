module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t1wi, t1wo, sw, cwli, cvo, dwi, t1wlo, t1vi extends Port  {
}

 fact {
   t1wi.tgt = t1wo + t1wlo
   t1wo.tgt = dwi
   sw.tgt = t1wi
   cwli.tgt = cvo
   cvo.tgt = t1vi
   no dwi.tgt
   t1wlo.tgt = cwli
   t1vi.tgt = t1wo
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 8