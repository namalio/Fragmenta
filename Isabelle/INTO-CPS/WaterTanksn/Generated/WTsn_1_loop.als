module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t1wi, t1wo, sw, cwli, cvo, dwi, t1wlo, t1vi, dwo extends Port  {
}

 fact {
   t1wi.tgt = t1wo + t1wlo
   t1wo.tgt = dwi
   sw.tgt = t1wi
   cwli.tgt = cvo
   cvo.tgt = t1vi
   dwi.tgt = dwo
   t1wlo.tgt = cwli
   t1vi.tgt = t1wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 9