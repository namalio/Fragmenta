module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t9wlo, t9vi, dwo extends Port  {
}

 fact {
   t9wi.tgt = t9wo + t9wlo
   t9wo.tgt = dwi
   t8wi.tgt = t8wo
   t8wo.tgt = t9wi
   t7wi.tgt = t7wo
   t7wo.tgt = t8wi
   t6wi.tgt = t6wo
   t6wo.tgt = t7wi
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
   sw.tgt = t9wi
   cwli.tgt = cvo
   cvo.tgt = t9vi
   dwi.tgt = dwo
   t9wlo.tgt = cwli
   t9vi.tgt = t9wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 25