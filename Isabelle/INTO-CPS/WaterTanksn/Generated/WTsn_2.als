module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t2wlo, t2vi extends Port  {
}

 fact {
   t2wi.tgt = t2wo + t2wlo
   t2wo.tgt = dwi
   t1wi.tgt = t1wo
   t1wo.tgt = t2wi
   sw.tgt = t2wi
   cwli.tgt = cvo
   cvo.tgt = t2vi
   no dwi.tgt
   t2wlo.tgt = cwli
   t2vi.tgt = t2wo
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 10