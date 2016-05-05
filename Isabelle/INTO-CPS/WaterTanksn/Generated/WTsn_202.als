module algebraicLoopCheck

abstract  sig Port {
   tgt :  set Port
}{
   tgt != this
}

 one sig t202win, t202wout, t201win, t201wout, t200win, t200wout, t199win, t199wout, t198win, t198wout, t197win, t197wout, t196win, t196wout, t195win, t195wout, t194win, t194wout, t193win, t193wout, t192win, t192wout, t191win, t191wout, t190win, t190wout, t189win, t189wout, t188win, t188wout, t187win, t187wout, t186win, t186wout, t185win, t185wout, t184win, t184wout, t183win, t183wout, t182win, t182wout, t181win, t181wout, t180win, t180wout, t179win, t179wout, t178win, t178wout, t177win, t177wout, t176win, t176wout, t175win, t175wout, t174win, t174wout, t173win, t173wout, t172win, t172wout, t171win, t171wout, t170win, t170wout, t169win, t169wout, t168win, t168wout, t167win, t167wout, t166win, t166wout, t165win, t165wout, t164win, t164wout, t163win, t163wout, t162win, t162wout, t161win, t161wout, t160win, t160wout, t159win, t159wout, t158win, t158wout, t157win, t157wout, t156win, t156wout, t155win, t155wout, t154win, t154wout, t153win, t153wout, t152win, t152wout, t151win, t151wout, t150win, t150wout, t149win, t149wout, t148win, t148wout, t147win, t147wout, t146win, t146wout, t145win, t145wout, t144win, t144wout, t143win, t143wout, t142win, t142wout, t141win, t141wout, t140win, t140wout, t139win, t139wout, t138win, t138wout, t137win, t137wout, t136win, t136wout, t135win, t135wout, t134win, t134wout, t133win, t133wout, t132win, t132wout, t131win, t131wout, t130win, t130wout, t129win, t129wout, t128win, t128wout, t127win, t127wout, t126win, t126wout, t125win, t125wout, t124win, t124wout, t123win, t123wout, t122win, t122wout, t121win, t121wout, t120win, t120wout, t119win, t119wout, t118win, t118wout, t117win, t117wout, t116win, t116wout, t115win, t115wout, t114win, t114wout, t113win, t113wout, t112win, t112wout, t111win, t111wout, t110win, t110wout, t109win, t109wout, t108win, t108wout, t107win, t107wout, t106win, t106wout, t105win, t105wout, t104win, t104wout, t103win, t103wout, t102win, t102wout, t101win, t101wout, t100win, t100wout, t99win, t99wout, t98win, t98wout, t97win, t97wout, t96win, t96wout, t95win, t95wout, t94win, t94wout, t93win, t93wout, t92win, t92wout, t91win, t91wout, t90win, t90wout, t89win, t89wout, t88win, t88wout, t87win, t87wout, t86win, t86wout, t85win, t85wout, t84win, t84wout, t83win, t83wout, t82win, t82wout, t81win, t81wout, t80win, t80wout, t79win, t79wout, t78win, t78wout, t77win, t77wout, t76win, t76wout, t75win, t75wout, t74win, t74wout, t73win, t73wout, t72win, t72wout, t71win, t71wout, t70win, t70wout, t69win, t69wout, t68win, t68wout, t67win, t67wout, t66win, t66wout, t65win, t65wout, t64win, t64wout, t63win, t63wout, t62win, t62wout, t61win, t61wout, t60win, t60wout, t59win, t59wout, t58win, t58wout, t57win, t57wout, t56win, t56wout, t55win, t55wout, t54win, t54wout, t53win, t53wout, t52win, t52wout, t51win, t51wout, t50win, t50wout, t49win, t49wout, t48win, t48wout, t47win, t47wout, t46win, t46wout, t45win, t45wout, t44win, t44wout, t43win, t43wout, t42win, t42wout, t41win, t41wout, t40win, t40wout, t39win, t39wout, t38win, t38wout, t37win, t37wout, t36win, t36wout, t35win, t35wout, t34win, t34wout, t33win, t33wout, t32win, t32wout, t31win, t31wout, t30win, t30wout, t29win, t29wout, t28win, t28wout, t27win, t27wout, t26win, t26wout, t25win, t25wout, t24win, t24wout, t23win, t23wout, t22win, t22wout, t21win, t21wout, t20win, t20wout, t19win, t19wout, t18win, t18wout, t17win, t17wout, t16win, t16wout, t15win, t15wout, t14win, t14wout, t13win, t13wout, t12win, t12wout, t11win, t11wout, t10win, t10wout, t9win, t9wout, t8win, t8wout, t7win, t7wout, t6win, t6wout, t5win, t5wout, t4win, t4wout, t3win, t3wout, t2win, t2wout, t1win, t1wout, iwout, cwlin, cvo, din, t202wlout, t202vi extends Port  {
}

 fact {
   t202win.tgt = t202wout + t202wlout
   t202wout.tgt = din
   t201win.tgt = t201wout
   t201wout.tgt = t202win
   t200win.tgt = t200wout
   t200wout.tgt = t201win
   t199win.tgt = t199wout
   t199wout.tgt = t200win
   t198win.tgt = t198wout
   t198wout.tgt = t199win
   t197win.tgt = t197wout
   t197wout.tgt = t198win
   t196win.tgt = t196wout
   t196wout.tgt = t197win
   t195win.tgt = t195wout
   t195wout.tgt = t196win
   t194win.tgt = t194wout
   t194wout.tgt = t195win
   t193win.tgt = t193wout
   t193wout.tgt = t194win
   t192win.tgt = t192wout
   t192wout.tgt = t193win
   t191win.tgt = t191wout
   t191wout.tgt = t192win
   t190win.tgt = t190wout
   t190wout.tgt = t191win
   t189win.tgt = t189wout
   t189wout.tgt = t190win
   t188win.tgt = t188wout
   t188wout.tgt = t189win
   t187win.tgt = t187wout
   t187wout.tgt = t188win
   t186win.tgt = t186wout
   t186wout.tgt = t187win
   t185win.tgt = t185wout
   t185wout.tgt = t186win
   t184win.tgt = t184wout
   t184wout.tgt = t185win
   t183win.tgt = t183wout
   t183wout.tgt = t184win
   t182win.tgt = t182wout
   t182wout.tgt = t183win
   t181win.tgt = t181wout
   t181wout.tgt = t182win
   t180win.tgt = t180wout
   t180wout.tgt = t181win
   t179win.tgt = t179wout
   t179wout.tgt = t180win
   t178win.tgt = t178wout
   t178wout.tgt = t179win
   t177win.tgt = t177wout
   t177wout.tgt = t178win
   t176win.tgt = t176wout
   t176wout.tgt = t177win
   t175win.tgt = t175wout
   t175wout.tgt = t176win
   t174win.tgt = t174wout
   t174wout.tgt = t175win
   t173win.tgt = t173wout
   t173wout.tgt = t174win
   t172win.tgt = t172wout
   t172wout.tgt = t173win
   t171win.tgt = t171wout
   t171wout.tgt = t172win
   t170win.tgt = t170wout
   t170wout.tgt = t171win
   t169win.tgt = t169wout
   t169wout.tgt = t170win
   t168win.tgt = t168wout
   t168wout.tgt = t169win
   t167win.tgt = t167wout
   t167wout.tgt = t168win
   t166win.tgt = t166wout
   t166wout.tgt = t167win
   t165win.tgt = t165wout
   t165wout.tgt = t166win
   t164win.tgt = t164wout
   t164wout.tgt = t165win
   t163win.tgt = t163wout
   t163wout.tgt = t164win
   t162win.tgt = t162wout
   t162wout.tgt = t163win
   t161win.tgt = t161wout
   t161wout.tgt = t162win
   t160win.tgt = t160wout
   t160wout.tgt = t161win
   t159win.tgt = t159wout
   t159wout.tgt = t160win
   t158win.tgt = t158wout
   t158wout.tgt = t159win
   t157win.tgt = t157wout
   t157wout.tgt = t158win
   t156win.tgt = t156wout
   t156wout.tgt = t157win
   t155win.tgt = t155wout
   t155wout.tgt = t156win
   t154win.tgt = t154wout
   t154wout.tgt = t155win
   t153win.tgt = t153wout
   t153wout.tgt = t154win
   t152win.tgt = t152wout
   t152wout.tgt = t153win
   t151win.tgt = t151wout
   t151wout.tgt = t152win
   t150win.tgt = t150wout
   t150wout.tgt = t151win
   t149win.tgt = t149wout
   t149wout.tgt = t150win
   t148win.tgt = t148wout
   t148wout.tgt = t149win
   t147win.tgt = t147wout
   t147wout.tgt = t148win
   t146win.tgt = t146wout
   t146wout.tgt = t147win
   t145win.tgt = t145wout
   t145wout.tgt = t146win
   t144win.tgt = t144wout
   t144wout.tgt = t145win
   t143win.tgt = t143wout
   t143wout.tgt = t144win
   t142win.tgt = t142wout
   t142wout.tgt = t143win
   t141win.tgt = t141wout
   t141wout.tgt = t142win
   t140win.tgt = t140wout
   t140wout.tgt = t141win
   t139win.tgt = t139wout
   t139wout.tgt = t140win
   t138win.tgt = t138wout
   t138wout.tgt = t139win
   t137win.tgt = t137wout
   t137wout.tgt = t138win
   t136win.tgt = t136wout
   t136wout.tgt = t137win
   t135win.tgt = t135wout
   t135wout.tgt = t136win
   t134win.tgt = t134wout
   t134wout.tgt = t135win
   t133win.tgt = t133wout
   t133wout.tgt = t134win
   t132win.tgt = t132wout
   t132wout.tgt = t133win
   t131win.tgt = t131wout
   t131wout.tgt = t132win
   t130win.tgt = t130wout
   t130wout.tgt = t131win
   t129win.tgt = t129wout
   t129wout.tgt = t130win
   t128win.tgt = t128wout
   t128wout.tgt = t129win
   t127win.tgt = t127wout
   t127wout.tgt = t128win
   t126win.tgt = t126wout
   t126wout.tgt = t127win
   t125win.tgt = t125wout
   t125wout.tgt = t126win
   t124win.tgt = t124wout
   t124wout.tgt = t125win
   t123win.tgt = t123wout
   t123wout.tgt = t124win
   t122win.tgt = t122wout
   t122wout.tgt = t123win
   t121win.tgt = t121wout
   t121wout.tgt = t122win
   t120win.tgt = t120wout
   t120wout.tgt = t121win
   t119win.tgt = t119wout
   t119wout.tgt = t120win
   t118win.tgt = t118wout
   t118wout.tgt = t119win
   t117win.tgt = t117wout
   t117wout.tgt = t118win
   t116win.tgt = t116wout
   t116wout.tgt = t117win
   t115win.tgt = t115wout
   t115wout.tgt = t116win
   t114win.tgt = t114wout
   t114wout.tgt = t115win
   t113win.tgt = t113wout
   t113wout.tgt = t114win
   t112win.tgt = t112wout
   t112wout.tgt = t113win
   t111win.tgt = t111wout
   t111wout.tgt = t112win
   t110win.tgt = t110wout
   t110wout.tgt = t111win
   t109win.tgt = t109wout
   t109wout.tgt = t110win
   t108win.tgt = t108wout
   t108wout.tgt = t109win
   t107win.tgt = t107wout
   t107wout.tgt = t108win
   t106win.tgt = t106wout
   t106wout.tgt = t107win
   t105win.tgt = t105wout
   t105wout.tgt = t106win
   t104win.tgt = t104wout
   t104wout.tgt = t105win
   t103win.tgt = t103wout
   t103wout.tgt = t104win
   t102win.tgt = t102wout
   t102wout.tgt = t103win
   t101win.tgt = t101wout
   t101wout.tgt = t102win
   t100win.tgt = t100wout
   t100wout.tgt = t101win
   t99win.tgt = t99wout
   t99wout.tgt = t100win
   t98win.tgt = t98wout
   t98wout.tgt = t99win
   t97win.tgt = t97wout
   t97wout.tgt = t98win
   t96win.tgt = t96wout
   t96wout.tgt = t97win
   t95win.tgt = t95wout
   t95wout.tgt = t96win
   t94win.tgt = t94wout
   t94wout.tgt = t95win
   t93win.tgt = t93wout
   t93wout.tgt = t94win
   t92win.tgt = t92wout
   t92wout.tgt = t93win
   t91win.tgt = t91wout
   t91wout.tgt = t92win
   t90win.tgt = t90wout
   t90wout.tgt = t91win
   t89win.tgt = t89wout
   t89wout.tgt = t90win
   t88win.tgt = t88wout
   t88wout.tgt = t89win
   t87win.tgt = t87wout
   t87wout.tgt = t88win
   t86win.tgt = t86wout
   t86wout.tgt = t87win
   t85win.tgt = t85wout
   t85wout.tgt = t86win
   t84win.tgt = t84wout
   t84wout.tgt = t85win
   t83win.tgt = t83wout
   t83wout.tgt = t84win
   t82win.tgt = t82wout
   t82wout.tgt = t83win
   t81win.tgt = t81wout
   t81wout.tgt = t82win
   t80win.tgt = t80wout
   t80wout.tgt = t81win
   t79win.tgt = t79wout
   t79wout.tgt = t80win
   t78win.tgt = t78wout
   t78wout.tgt = t79win
   t77win.tgt = t77wout
   t77wout.tgt = t78win
   t76win.tgt = t76wout
   t76wout.tgt = t77win
   t75win.tgt = t75wout
   t75wout.tgt = t76win
   t74win.tgt = t74wout
   t74wout.tgt = t75win
   t73win.tgt = t73wout
   t73wout.tgt = t74win
   t72win.tgt = t72wout
   t72wout.tgt = t73win
   t71win.tgt = t71wout
   t71wout.tgt = t72win
   t70win.tgt = t70wout
   t70wout.tgt = t71win
   t69win.tgt = t69wout
   t69wout.tgt = t70win
   t68win.tgt = t68wout
   t68wout.tgt = t69win
   t67win.tgt = t67wout
   t67wout.tgt = t68win
   t66win.tgt = t66wout
   t66wout.tgt = t67win
   t65win.tgt = t65wout
   t65wout.tgt = t66win
   t64win.tgt = t64wout
   t64wout.tgt = t65win
   t63win.tgt = t63wout
   t63wout.tgt = t64win
   t62win.tgt = t62wout
   t62wout.tgt = t63win
   t61win.tgt = t61wout
   t61wout.tgt = t62win
   t60win.tgt = t60wout
   t60wout.tgt = t61win
   t59win.tgt = t59wout
   t59wout.tgt = t60win
   t58win.tgt = t58wout
   t58wout.tgt = t59win
   t57win.tgt = t57wout
   t57wout.tgt = t58win
   t56win.tgt = t56wout
   t56wout.tgt = t57win
   t55win.tgt = t55wout
   t55wout.tgt = t56win
   t54win.tgt = t54wout
   t54wout.tgt = t55win
   t53win.tgt = t53wout
   t53wout.tgt = t54win
   t52win.tgt = t52wout
   t52wout.tgt = t53win
   t51win.tgt = t51wout
   t51wout.tgt = t52win
   t50win.tgt = t50wout
   t50wout.tgt = t51win
   t49win.tgt = t49wout
   t49wout.tgt = t50win
   t48win.tgt = t48wout
   t48wout.tgt = t49win
   t47win.tgt = t47wout
   t47wout.tgt = t48win
   t46win.tgt = t46wout
   t46wout.tgt = t47win
   t45win.tgt = t45wout
   t45wout.tgt = t46win
   t44win.tgt = t44wout
   t44wout.tgt = t45win
   t43win.tgt = t43wout
   t43wout.tgt = t44win
   t42win.tgt = t42wout
   t42wout.tgt = t43win
   t41win.tgt = t41wout
   t41wout.tgt = t42win
   t40win.tgt = t40wout
   t40wout.tgt = t41win
   t39win.tgt = t39wout
   t39wout.tgt = t40win
   t38win.tgt = t38wout
   t38wout.tgt = t39win
   t37win.tgt = t37wout
   t37wout.tgt = t38win
   t36win.tgt = t36wout
   t36wout.tgt = t37win
   t35win.tgt = t35wout
   t35wout.tgt = t36win
   t34win.tgt = t34wout
   t34wout.tgt = t35win
   t33win.tgt = t33wout
   t33wout.tgt = t34win
   t32win.tgt = t32wout
   t32wout.tgt = t33win
   t31win.tgt = t31wout
   t31wout.tgt = t32win
   t30win.tgt = t30wout
   t30wout.tgt = t31win
   t29win.tgt = t29wout
   t29wout.tgt = t30win
   t28win.tgt = t28wout
   t28wout.tgt = t29win
   t27win.tgt = t27wout
   t27wout.tgt = t28win
   t26win.tgt = t26wout
   t26wout.tgt = t27win
   t25win.tgt = t25wout
   t25wout.tgt = t26win
   t24win.tgt = t24wout
   t24wout.tgt = t25win
   t23win.tgt = t23wout
   t23wout.tgt = t24win
   t22win.tgt = t22wout
   t22wout.tgt = t23win
   t21win.tgt = t21wout
   t21wout.tgt = t22win
   t20win.tgt = t20wout
   t20wout.tgt = t21win
   t19win.tgt = t19wout
   t19wout.tgt = t20win
   t18win.tgt = t18wout
   t18wout.tgt = t19win
   t17win.tgt = t17wout
   t17wout.tgt = t18win
   t16win.tgt = t16wout
   t16wout.tgt = t17win
   t15win.tgt = t15wout
   t15wout.tgt = t16win
   t14win.tgt = t14wout
   t14wout.tgt = t15win
   t13win.tgt = t13wout
   t13wout.tgt = t14win
   t12win.tgt = t12wout
   t12wout.tgt = t13win
   t11win.tgt = t11wout
   t11wout.tgt = t12win
   t10win.tgt = t10wout
   t10wout.tgt = t11win
   t9win.tgt = t9wout
   t9wout.tgt = t10win
   t8win.tgt = t8wout
   t8wout.tgt = t9win
   t7win.tgt = t7wout
   t7wout.tgt = t8win
   t6win.tgt = t6wout
   t6wout.tgt = t7win
   t5win.tgt = t5wout
   t5wout.tgt = t6win
   t4win.tgt = t4wout
   t4wout.tgt = t5win
   t3win.tgt = t3wout
   t3wout.tgt = t4win
   t2win.tgt = t2wout
   t2wout.tgt = t3win
   t1win.tgt = t1wout
   t1wout.tgt = t2win
   iwout.tgt = t1win
   cwlin.tgt = cvo
   cvo.tgt = t202vi
   no din.tgt
   t202wlout.tgt = cwlin
   t202vi.tgt = t202wout
}

 assert AcyclicTgt {
   no ^tgt & iden
}

 check AcyclicTgt for 410