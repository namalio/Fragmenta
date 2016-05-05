module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t7wlo, t7vi extends Port  {
}

 fact {
   t7wi.tgt = t7wo + t7wlo
   t7wo.tgt = dwi
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
   sw.tgt = t7wi
   cwli.tgt = cvo
   cvo.tgt = t7vi
   no dwi.tgt
   t7wlo.tgt = cwli
   t7vi.tgt = t7wo
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 20