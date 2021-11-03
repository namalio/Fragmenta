module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t3wlo, t3vi, dwo extends Port  {
}

 fact {
   t3wi.tgt = t3wo + t3wlo
   t3wo.tgt = dwi
   t2wi.tgt = t2wo
   t2wo.tgt = t3wi
   t1wi.tgt = t1wo
   t1wo.tgt = t2wi
   sw.tgt = t3wi
   cwli.tgt = cvo
   cvo.tgt = t3vi
   dwi.tgt = dwo
   t3wlo.tgt = cwli
   t3vi.tgt = t3wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 13