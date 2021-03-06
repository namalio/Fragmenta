module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t25wi, t25wo, t24wi, t24wo, t23wi, t23wo, t22wi, t22wo, t21wi, t21wo, t20wi, t20wo, t19wi, t19wo, t18wi, t18wo, t17wi, t17wo, t16wi, t16wo, t15wi, t15wo, t14wi, t14wo, t13wi, t13wo, t12wi, t12wo, t11wi, t11wo, t10wi, t10wo, t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t25wlo, t25vi, dwo extends Port  {
}

 fact {
   t25wi.tgt = t25wo + t25wlo
   t25wo.tgt = dwi
   t24wi.tgt = t24wo
   t24wo.tgt = t25wi
   t23wi.tgt = t23wo
   t23wo.tgt = t24wi
   t22wi.tgt = t22wo
   t22wo.tgt = t23wi
   t21wi.tgt = t21wo
   t21wo.tgt = t22wi
   t20wi.tgt = t20wo
   t20wo.tgt = t21wi
   t19wi.tgt = t19wo
   t19wo.tgt = t20wi
   t18wi.tgt = t18wo
   t18wo.tgt = t19wi
   t17wi.tgt = t17wo
   t17wo.tgt = t18wi
   t16wi.tgt = t16wo
   t16wo.tgt = t17wi
   t15wi.tgt = t15wo
   t15wo.tgt = t16wi
   t14wi.tgt = t14wo
   t14wo.tgt = t15wi
   t13wi.tgt = t13wo
   t13wo.tgt = t14wi
   t12wi.tgt = t12wo
   t12wo.tgt = t13wi
   t11wi.tgt = t11wo
   t11wo.tgt = t12wi
   t10wi.tgt = t10wo
   t10wo.tgt = t11wi
   t9wi.tgt = t9wo
   t9wo.tgt = t10wi
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
   sw.tgt = t25wi
   cwli.tgt = cvo
   cvo.tgt = t25vi
   dwi.tgt = dwo
   t25wlo.tgt = cwli
   t25vi.tgt = t25wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 57