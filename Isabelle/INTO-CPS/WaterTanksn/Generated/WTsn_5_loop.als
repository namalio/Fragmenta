module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t5wlo, t5vi, dwo extends Port  {
}

 fact {
   t5wi.tgt = t5wo + t5wlo
   t5wo.tgt = dwi
   t4wi.tgt = t4wo
   t4wo.tgt = t5wi
   t3wi.tgt = t3wo
   t3wo.tgt = t4wi
   t2wi.tgt = t2wo
   t2wo.tgt = t3wi
   t1wi.tgt = t1wo
   t1wo.tgt = t2wi
   sw.tgt = t5wi
   cwli.tgt = cvo
   cvo.tgt = t5vi
   dwi.tgt = dwo
   t5wlo.tgt = cwli
   t5vi.tgt = t5wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 17