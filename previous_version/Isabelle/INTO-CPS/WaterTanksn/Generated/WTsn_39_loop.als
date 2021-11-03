module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t39wi, t39wo, t38wi, t38wo, t37wi, t37wo, t36wi, t36wo, t35wi, t35wo, t34wi, t34wo, t33wi, t33wo, t32wi, t32wo, t31wi, t31wo, t30wi, t30wo, t29wi, t29wo, t28wi, t28wo, t27wi, t27wo, t26wi, t26wo, t25wi, t25wo, t24wi, t24wo, t23wi, t23wo, t22wi, t22wo, t21wi, t21wo, t20wi, t20wo, t19wi, t19wo, t18wi, t18wo, t17wi, t17wo, t16wi, t16wo, t15wi, t15wo, t14wi, t14wo, t13wi, t13wo, t12wi, t12wo, t11wi, t11wo, t10wi, t10wo, t9wi, t9wo, t8wi, t8wo, t7wi, t7wo, t6wi, t6wo, t5wi, t5wo, t4wi, t4wo, t3wi, t3wo, t2wi, t2wo, t1wi, t1wo, sw, cwli, cvo, dwi, t39wlo, t39vi, dwo extends Port  {
}

 fact {
   t39wi.tgt = t39wo + t39wlo
   t39wo.tgt = dwi
   t38wi.tgt = t38wo
   t38wo.tgt = t39wi
   t37wi.tgt = t37wo
   t37wo.tgt = t38wi
   t36wi.tgt = t36wo
   t36wo.tgt = t37wi
   t35wi.tgt = t35wo
   t35wo.tgt = t36wi
   t34wi.tgt = t34wo
   t34wo.tgt = t35wi
   t33wi.tgt = t33wo
   t33wo.tgt = t34wi
   t32wi.tgt = t32wo
   t32wo.tgt = t33wi
   t31wi.tgt = t31wo
   t31wo.tgt = t32wi
   t30wi.tgt = t30wo
   t30wo.tgt = t31wi
   t29wi.tgt = t29wo
   t29wo.tgt = t30wi
   t28wi.tgt = t28wo
   t28wo.tgt = t29wi
   t27wi.tgt = t27wo
   t27wo.tgt = t28wi
   t26wi.tgt = t26wo
   t26wo.tgt = t27wi
   t25wi.tgt = t25wo
   t25wo.tgt = t26wi
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
   sw.tgt = t39wi
   cwli.tgt = cvo
   cvo.tgt = t39vi
   dwi.tgt = dwo
   t39wlo.tgt = cwli
   t39vi.tgt = t39wo
   dwo.tgt = t1wi
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 85