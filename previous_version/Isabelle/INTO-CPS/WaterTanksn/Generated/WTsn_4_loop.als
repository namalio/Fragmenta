module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t4wlo, t4vi, dwo extends Port  {
}

 fact {
   t4wi.tgt = t4wo + t4wlo
   t4wo.tgt = dwi
   t3wi.tgt = t3wo
   t3wo.tgt = t4wi
   t2wi.tgt = t2wo
   t2wo.tgt = t3wi
   t1wi.tgt = t1wo
   t1wo.tgt = t2wi
   sw.tgt = t4wi
   cwli.tgt = cvo
   cvo.tgt = t4vi
   dwi.tgt = dwo
   t4wlo.tgt = cwli
   t4vi.tgt = t4wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 15