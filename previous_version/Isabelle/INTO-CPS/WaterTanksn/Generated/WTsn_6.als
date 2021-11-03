module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t6wlo, t6vi extends Port  {
}

 fact {
   t6wi.tgt = t6wo + t6wlo
   t6wo.tgt = dwi
   t5wi.tgt = t5wo
   t5wo.tgt = t6wi
   t4wi.tgt = t4wo
   t4wo.tgt = t5wi
   t3wi.tgt = t3wo
   t3wo.tgt = t4wi
   t2wi.tgt = t2wo
   t2wo.tgt = t3wi
   t1wi.tgt = t1wo
   t1wo.tgt = t2wi
   sw.tgt = t6wi
   cwli.tgt = cvo
   cvo.tgt = t6vi
   no dwi.tgt
   t6wlo.tgt = cwli
   t6vi.tgt = t6wo
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 18