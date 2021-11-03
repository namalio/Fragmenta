
(*  File:      'INTO_SysML_3WTsPilot_CD' 
    Description: The CD enconding of the INTO-SysML model of the pilot case study of 3 Water tanks 
    Author:     Nuno Amálio
*)

theory INTO_SysML_3WTsPilot_CD
imports INTO_SysML_3WTsPilot_ASD
  
begin

definition SG_CD_3WTsP :: "SGr_ls"
where
  "SG_CD_3WTsP = \<lparr>
    NsG=[''PrTankIO'', ''PrTankIOV'', ''PrInflow'', ''PrPipe'', ''PrDrain'', 
      ''PrWaterTanks1'', 
      ''PrWaterTanks2'', ''PrController'', ''CD_3WTs'', ''WTSys'',
      ''I'', ''P'', ''T1'', ''T2'', ''T3'',  ''C'', ''D'', ''WT1'', ''WT2'',
      ''iout'', ''t1in'', ''t1out'', ''pin'', ''pout'', ''t2in'', ''t2out'', 
      ''wout'', ''win'', ''wlout'', ''vi1'', ''t3in'', ''t3wlout'', ''t3out'', ''vi2'',   
      ''din'', ''din'', ''wlin'', ''vo'',
      ''C_iout_t1in'', ''C_t1out_pin'', ''C_pout_t2in2'', ''C_t2out_wout'',
      ''C_wout_win'', ''C_win_t3in'', ''C_t3wlout_wlout'', ''C_t3out_din'',
      ''C_wlout_wlin'', ''C_vo_vi1'', ''C_vi1_vi2'',
      ''PrInflow_wout'', ''PrTankIO_win'', ''PrTankIO_wout'', ''PrPipe_win'',
      ''PrPipe_wout'', ''PrWaterTanks1_wout'', ''PrWaterTanks2_win'', 
      ''PrWaterTanks2_wlout'', ''PrWaterTanks2_vi'',
      ''PrController_wlin'', ''PrController_vo'', ''PrDrain_win'', 
      ''PrTankIOV_win'', ''PrTankIOV_wout'', ''PrTankIOV_wlout'', 
      ''PrTankIOV_vi''], 
    EsG = [''ECD_WTSys'', ''ECD_I'', ''ECD_P'', ''ECD_T1'', ''ECD_T2'', 
      ''ECD_T3'', ''ECD_C'', ''ECD_D'', ''ECD_WT1'', ''ECD_WT2'', 
      ''ECD_C_iout_t1in'', ''ECD_C_t1out_pin'', ''ECD_C_pout_t2in2'', ''ECD_C_t2out_wout'',
      ''ECD_C_wout_win'', ''ECD_C_win_t3in'', ''ECD_C_t3wlout_wlout'', ''ECD_C_t3out_din'',
      ''ECD_C_wlout_wlin'', ''ECD_C_vo_vi1'', ''ECD_C_vi1_vi2'',
      ''E_WTSys_WT1'', ''E_WTSys_WT2'', ''E_WTSys_C'',
      ''E_WT1_I'', ''E_WT1_P'', ''E_WT1_T1'', ''E_WT1_T2'', 
      ''E_WT2_T3'', ''E_WT2_D'', 
      ''E_I_iout'', ''E_P_pin'', ''E_P_pout'', ''E_T1_t1in'', ''E_T1_t1out'', 
      ''E_T2_t2in'', ''E_T2_t2out'', 
      ''E_T3_t3in'', ''E_T3_t3wlout'', ''E_T3_vi2'', 
      ''E_C_wlin'', ''E_C_vo'', ''E_D_din'', ''E_WT1_wout'', ''E_WT2_win'', 
      ''E_WT2_wlout'', ''E_WT2_vi1'',
      ''E_C_iout_t1in_src'', ''E_C_iout_t1in_tgt'', 
      ''E_C_t1out_pin_src'', ''E_C_t1out_pin_tgt'', 
      ''E_C_pout_t2in_src'', ''E_C_pout_t2in_tgt'',
      ''E_C_t2out_wout_src'', ''E_C_t2out_wout_tgt'',
      ''E_C_wout_win_src'', ''E_C_wout_win_tgt'', 
      ''E_C_win_t3in_src'', ''E_C_win_t3in_tgt'', 
      ''E_C_t3wlout_wlout_src'', ''E_C_t3wlout_wlout_tgt'', 
      ''E_C_t3out_din_src'', ''E_C_t3out_din_tgt'',
      ''E_C_wlout_wlin_src'', ''E_C_wlout_wlin_tgt'', 
      ''E_C_vo_vi1_src'', ''E_C_vo_vi1_tgt'', 
      ''E_C_vi1_vi2_src'', ''E_C_vi1_vi2_tgt'',
      ''E_iout_ty'', ''E_t1in_ty'', ''E_t1out_ty'', ''E_pin_ty'', ''E_pout_ty'', ''E_t2in_ty'', 
      ''E_t2out_ty'', ''E_wout_ty'', ''E_win_ty'', ''E_wlout_ty'', ''E_vi1_ty'', 
      ''E_t3in_ty'', ''E_t3wlout_ty'', ''E_t3out_ty'', ''E_vi2_ty'',   
      ''E_din_ty'', ''E_wlin_ty'', ''E_vo_ty'',
      ''ERPrTankIO'', ''ERPrTankIOV'', ''ERPrInflow'', ''ERPrPipe'', ''ERPrDrain'', 
      ''ERPrWaterTanks1'', ''ERPrWaterTanks2'', ''ERPrController'',
      ''ERPrInflow_wout'', ''ERPrTankIO_win'', ''ERPrTankIO_wout'', ''ERPrPipe_win'',
      ''ERPrPipe_wout'', ''ERPrWaterTanks1_wout'', ''ERPrWaterTanks2_win'', 
      ''ERPrWaterTanks2_wlout'', ''ERPrWaterTanks2_vi'',
      ''ERPrController_wlin'', ''ERPrController_vo'', ''ERPrDrain_win'', 
      ''ERPrTankIOV_win'', ''ERPrTankIOV_wout'', ''ERPrTankIOV_wlout'', 
      ''ERPrTankIOV_vi''], 
    srcG =  [
      (''ECD_WTSys'', ''CD_3WTs''), (''ECD_I'', ''CD_3WTs''), 
      (''ECD_P'', ''CD_3WTs''), (''ECD_T1'', ''CD_3WTs''), 
      (''ECD_T2'', ''CD_3WTs''), (''ECD_T3'', ''CD_3WTs''), 
      (''ECD_C'', ''CD_3WTs''), (''ECD_D'', ''CD_3WTs''),
      (''ECD_WT1'', ''CD_3WTs''), (''ECD_WT2'', ''CD_3WTs''),
      (''ECD_C_iout_t1in'', ''CD_3WTs''), (''ECD_C_t1out_pin'', ''CD_3WTs''), 
      (''ECD_C_pout_t2in2'', ''CD_3WTs''), (''ECD_C_t2out_wout'', ''CD_3WTs''),
      (''ECD_C_wout_win'', ''CD_3WTs''), (''ECD_C_win_t3in'', ''CD_3WTs''),
      (''ECD_C_t3wlout_wlout'', ''CD_3WTs''), (''ECD_C_t3out_din'', ''CD_3WTs''),
      (''ECD_C_wlout_wlin'', ''CD_3WTs''), (''ECD_C_vo_vi1'', ''CD_3WTs''), 
      (''ECD_C_vi1_vi2'', ''CD_3WTs''),
      (''E_WTSys_WT1'', ''WTSys''), (''E_WTSys_WT2'', ''WTSys''), 
      (''E_WTSys_C'', ''WTSys''), (''E_WT1_I'', ''WT1''),
      (''E_WT1_P'', ''WT1''), (''E_WT1_T1'', ''WT1''), (''E_WT1_T2'', ''WT1''),
      (''E_WT2_T3'', ''WT2''), (''E_WT2_D'', ''WT2''),
      (''E_I_iout'', ''I''), (''E_P_pin'', ''P''), 
      (''E_P_pout'', ''P''), (''E_T1_t1in'', ''T1''), 
      (''E_T1_t1out'', ''T1''), (''E_T2_t2in'', ''T2''),
      (''E_T2_t2out'', ''T2''), (''E_T3_t3in'', ''T3''), 
      (''E_T3_t3wlout'', ''T3''), (''E_T3_vi2'', ''T3''),
      (''E_C_wlin'', ''C''), (''E_C_vo'', ''C''), (''E_D_din'', ''D''),
      (''E_WT1_wout'', ''WT1''), (''E_WT2_win'', ''WT2''),
      (''E_WT2_wlout'', ''WT2''), (''E_WT2_vi1'', ''WT2''),
      (''E_C_iout_t1in_src'', ''C_iout_t1in''), 
      (''E_C_iout_t1in_tgt'', ''C_iout_t1in''),
      (''E_C_t1out_pin_src'', ''C_t1out_pin''), 
      (''E_C_t1out_pin_tgt'', ''C_t1out_pin''),
      (''E_C_pout_t2in_src'', ''C_pout_t2in2''), 
      (''E_C_pout_t2in_tgt'', ''C_pout_t2in2''),
      (''E_C_t2out_wout_src'', ''C_t2out_wout''), 
      (''E_C_t2out_wout_tgt'', ''C_t2out_wout''),
      (''E_C_wout_win_src'', ''C_wout_win''), 
      (''E_C_wout_win_tgt'', ''C_wout_win''), 
      (''E_C_win_t3in_src'', ''C_win_t3in''),
      (''E_C_win_t3in_tgt'', ''C_win_t3in''),
      (''E_C_t3wlout_wlout_src'', ''C_t3wlout_wlout''), 
      (''E_C_t3wlout_wlout_tgt'', ''C_t3wlout_wlout''),
      (''E_C_t3out_din_src'', ''C_t3out_din''),
      (''E_C_t3out_din_tgt'', ''C_t3out_din''),
      (''E_C_wlout_wlin_src'', ''C_wlout_wlin''),
      (''E_C_wlout_wlin_tgt'', ''C_wlout_wlin''),
      (''E_C_vo_vi1_src'', ''C_vo_vi1''),
      (''E_C_vo_vi1_tgt'', ''C_vo_vi1''),
      (''E_C_vi1_vi2_src'', ''C_vi1_vi2''), 
      (''E_C_vi1_vi2_tgt'', ''C_vi1_vi2''), 
      (''E_iout_ty'', ''iout''), (''E_t1in_ty'', ''t1in''), 
      (''E_t1out_ty'', ''t1out''), (''E_pin_ty'', ''pin''), 
      (''E_pout_ty'', ''pout''), (''E_t2in_ty'', ''t2in''),
      (''E_t2out_ty'', ''t2out''), (''E_wout_ty'', ''wout''),
      (''E_win_ty'', ''win''), (''E_wlout_ty'', ''wlout''),
      (''E_vi1_ty'', ''vi1''), (''E_t3in_ty'', ''t3in''), 
      (''E_t3wlout_ty'', ''t3wlout''), (''E_t3out_ty'', ''t3out''),
      (''E_vi2_ty'', ''vi2''), (''E_din_ty'', ''din''), 
      (''E_wlin_ty'', ''wlin''), (''E_vo_ty'', ''vo''),
      (''ERPrTankIO'', ''PrTankIO''), 
      (''ERPrTankIOV'', ''PrTankIOV''), (''ERPrInflow'', ''PrInflow''),
      (''ERPrPipe'', ''PrPipe''), (''ERPrDrain'', ''PrDrain''),
      (''ERPrWaterTanks1'', ''PrWaterTanks1''), (''ERPrWaterTanks2'', ''PrWaterTanks2''),
      (''ERPrController'', ''PrController''), 
      (''ERPrInflow_wout'', ''PrInflow_wout''), 
      (''ERPrTankIO_win'', ''PrTankIO_win''), (''ERPrTankIO_wout'', ''PrTankIO_wout''), 
      (''ERPrPipe_win'', ''PrPipe_win''), 
      (''ERPrPipe_wout'', ''PrPipe_wout''), 
      (''ERPrWaterTanks1_wout'', ''PrWaterTanks1_wout''), 
      (''ERPrWaterTanks2_win'', ''PrWaterTanks2_win''),
      (''ERPrWaterTanks2_wlout'', ''PrWaterTanks2_wlout''), 
      (''ERPrWaterTanks2_vi'', ''PrWaterTanks2_vi''),
      (''ERPrController_wlin'', ''PrController_wlin''),
      (''ERPrController_vo'', ''PrController_vo''),
      (''ERPrDrain_win'', ''PrDrain_win''), 
      (''ERPrTankIOV_win'', ''PrTankIOV_win''), 
      (''ERPrTankIOV_wout'', ''PrTankIOV_wout''), 
      (''ERPrTankIOV_wlout'', ''PrTankIOV_wlout''),
      (''ERPrTankIOV_vi'', ''PrTankIOV_vi'')],
    tgtG =  [
      (''ECD_WTSys'', ''WTSys''), (''ECD_I'', ''I''), 
      (''ECD_P'', ''P''), (''ECD_T1'', ''T1''), 
      (''ECD_T2'', ''T2''), (''ECD_T3'', ''T3''), 
      (''ECD_C'', ''C''), (''ECD_D'', ''D''),
      (''ECD_WT1'', ''WT1''), (''ECD_WT2'', ''WT2''),
      (''ECD_C_iout_t1in'', ''C_iout_t1in''), 
      (''ECD_C_t1out_pin'', ''C_t1out_pin''), 
      (''ECD_C_pout_t2in2'', ''C_pout_t2in2''), 
      (''ECD_C_t2out_wout'', ''C_t2out_wout''),
      (''ECD_C_wout_win'', ''C_wout_win''), (''ECD_C_win_t3in'', ''C_win_t3in''),
      (''ECD_C_t3wlout_wlout'', ''C_t3wlout_wlout''), (''ECD_C_t3out_din'', ''C_t3out_din''),
      (''ECD_C_wlout_wlin'', ''C_wlout_wlin''), (''ECD_C_vo_vi1'', ''C_vo_vi1''), 
      (''ECD_C_vi1_vi2'', ''C_vi1_vi2''),
      (''E_WTSys_WT1'', ''WT1''), (''E_WTSys_WT2'', ''WT2''), 
      (''E_WTSys_C'', ''C''), (''E_WT1_I'', ''I''),
      (''E_WT1_P'', ''P''), (''E_WT1_T1'', ''T1''), (''E_WT1_T2'', ''T2''),
      (''E_WT2_T3'', ''T3''), (''E_WT2_D'', ''D''),
      (''E_I_iout'', ''iout''), (''E_P_pin'', ''pin''), 
      (''E_P_pout'', ''pout''), (''E_T1_t1in'', ''t1in''), 
      (''E_T1_t1out'', ''t1out''), (''E_T2_t2in'', ''t2in''),
      (''E_T2_t2out'', ''t2out''), (''E_T3_t3in'', ''t3in''), 
      (''E_T3_t3wlout'', ''t3wlout''), (''E_T3_vi2'', ''vi2''),
      (''E_C_wlin'', ''wlin''), (''E_C_vo'', ''vo''), (''E_D_din'', ''din''),
      (''E_WT1_wout'', ''wout''), (''E_WT2_win'', ''win''),
      (''E_WT2_wlout'', ''wlout''), (''E_WT2_vi1'', ''vi1''),
      (''E_C_iout_t1in_src'', ''iout''), 
      (''E_C_iout_t1in_tgt'', ''t1in''),
      (''E_C_t1out_pin_src'', ''t1out''), 
      (''E_C_t1out_pin_tgt'', ''pin''),
      (''E_C_pout_t2in_src'', ''pout''), 
      (''E_C_pout_t2in_tgt'', ''t2in''),
      (''E_C_t2out_wout_src'', ''t2out''), 
      (''E_C_t2out_wout_tgt'', ''wout''),
      (''E_C_wout_win_src'', ''wout''), 
      (''E_C_wout_win_tgt'', ''win''), 
      (''E_C_win_t3in_src'', ''win''),
      (''E_C_win_t3in_tgt'', ''t3in''),
      (''E_C_t3wlout_wlout_src'', ''t3wlout''), 
      (''E_C_t3wlout_wlout_tgt'', ''wlout''),
      (''E_C_t3out_din_src'', ''t3out''),
      (''E_C_t3out_din_tgt'', ''din''),
      (''E_C_wlout_wlin_src'', ''wlout''),
      (''E_C_wlout_wlin_tgt'', ''wlin''),
      (''E_C_vo_vi1_src'', ''vo''),
      (''E_C_vo_vi1_tgt'', ''vi1''),
      (''E_C_vi1_vi2_src'', ''vi1''), 
      (''E_C_vi1_vi2_tgt'', ''vi2''), 
      (''E_iout_ty'', ''PrInflow_wout''), 
      (''E_t1in_ty'', ''PrTankIO_win''), 
      (''E_t1out_ty'', ''PrTankIO_wout''), 
      (''E_pin_ty'', ''PrPipe_win''), 
      (''E_pout_ty'', ''PrPipe_wout''), 
      (''E_t2in_ty'', ''PrTankIO_win''),
      (''E_t2out_ty'', ''PrTankIO_wout''), 
      (''E_wout_ty'', ''PrWaterTanks1_wout''),
      (''E_win_ty'', ''PrWaterTanks2_win''), 
      (''E_wlout_ty'', ''PrWaterTanks2_wlout''),
      (''E_vi1_ty'', ''PrWaterTanks2_vi''), 
      (''E_t3in_ty'', ''PrTankIOV_win''), 
      (''E_t3wlout_ty'', ''PrTankIOV_wlout''), (''E_t3out_ty'', ''PrTankIOV_wout''),
      (''E_vi2_ty'', ''PrTankIOV_vi''), (''E_din_ty'', ''PrDrain_win''), 
      (''E_wlin_ty'', ''PrController_wlin''), (''E_vo_ty'', ''PrController_vo''),
      (''ERPrTankIO'', ''PrTankIO''), 
      (''ERPrTankIOV'', ''PrTankIOV''), (''ERPrInflow'', ''PrInflow''),
      (''ERPrPipe'', ''PrPipe''), (''ERPrDrain'', ''PrDrain''),
      (''ERPrWaterTanks1'', ''PrWaterTanks1''), (''ERPrWaterTanks2'', ''PrWaterTanks2''),
      (''ERPrController'', ''PrController''), 
      (''ERPrInflow_wout'', ''PrInflow_wout''), 
      (''ERPrTankIO_win'', ''PrTankIO_win''), (''ERPrTankIO_wout'', ''PrTankIO_wout''), 
      (''ERPrPipe_win'', ''PrPipe_win''), 
      (''ERPrPipe_wout'', ''PrPipe_wout''), 
      (''ERPrWaterTanks1_wout'', ''PrWaterTanks1_wout''), 
      (''ERPrWaterTanks2_win'', ''PrWaterTanks2_win''),
      (''ERPrWaterTanks2_wlout'', ''PrWaterTanks2_wlout''), 
      (''ERPrWaterTanks2_vi'', ''PrWaterTanks2_vi''),
      (''ERPrController_wlin'', ''PrController_wlin''),
      (''ERPrController_vo'', ''PrController_vo''),
      (''ERPrDrain_win'', ''PrDrain_win''), 
      (''ERPrTankIOV_win'', ''PrTankIOV_win''), 
      (''ERPrTankIOV_wout'', ''PrTankIOV_wout''), 
      (''ERPrTankIOV_wlout'', ''PrTankIOV_wlout''),
      (''ERPrTankIOV_vi'', ''PrTankIOV_vi'')],
   ntyG =[(''PrTankIO'', nprxy), (''PrTankIOV'', nprxy), (''PrInflow'', nprxy), 
    (''PrPipe'', nprxy), (''PrDrain'', nprxy),
    (''PrWaterTanks1'', nprxy), (''PrWaterTanks2'', nprxy), 
    (''PrController'', nprxy), (''CD_3WTs'', nnrml), (''WTSys'', nnrml),
    (''I'', nnrml), (''P'', nnrml), (''T1'', nnrml), (''T2'', nnrml), (''T3'', nnrml),
    (''C'', nnrml), (''D'', nnrml), (''WT1'', nnrml), (''WT2'', nnrml),
    (''iout'', nnrml), (''t1in'', nnrml), (''t1out'', nnrml), (''pin'', nnrml), 
    (''pout'', nnrml), (''t2in'', nnrml), (''t2out'', nnrml),
    (''wout'', nnrml), (''win'', nnrml), (''wlout'', nnrml), (''vi1'', nnrml),
    (''t3in'', nnrml), (''t3wlout'', nnrml), (''t3out'', nnrml), (''vi2'', nnrml), 
    (''din'', nnrml), (''din'', nnrml), (''wlin'', nnrml), (''vo'', nnrml),
    (''C_iout_t1in'', nnrml), (''C_t1out_pin'', nnrml), (''C_pout_t2in2'', nnrml),
    (''C_t2out_wout'', nnrml), (''C_wout_win'', nnrml), (''C_win_t3in'', nnrml), 
    (''C_t3wlout_wlout'', nnrml), (''C_t3out_din'', nnrml),
    (''C_wlout_wlin'', nnrml), (''C_vo_vi1'', nnrml), (''C_vi1_vi2'', nnrml),
    (''PrInflow_wout'', nprxy), (''PrTankIO_win'', nprxy), (''PrTankIO_wout'', nprxy), 
    (''PrPipe_win'', nprxy), (''PrPipe_wout'', nprxy), (''PrWaterTanks1_wout'', nprxy), 
    (''PrWaterTanks2_win'', nprxy), (''PrWaterTanks2_wlout'', nprxy), 
    (''PrWaterTanks2_vi'', nprxy), (''PrController_wlin'', nprxy), 
    (''PrController_vo'', nprxy), (''PrDrain_win'', nprxy),
    (''PrTankIOV_win'', nprxy), (''PrTankIOV_wout'', nprxy), (''PrTankIOV_wlout'', nprxy),
    (''PrTankIOV_vi'', nprxy)],
      etyG =[
        (''ECD_WTSys'', elnk), (''ECD_I'', elnk), 
      (''ECD_P'', elnk), (''ECD_T1'', elnk), 
      (''ECD_T2'', elnk), (''ECD_T3'', elnk), 
      (''ECD_C'', elnk), (''ECD_D'', elnk),
      (''ECD_WT1'', elnk), (''ECD_WT2'', elnk),
      (''ECD_C_iout_t1in'', elnk), 
      (''ECD_C_t1out_pin'', elnk), 
      (''ECD_C_pout_t2in2'', elnk), 
      (''ECD_C_t2out_wout'', elnk),
      (''ECD_C_wout_win'', elnk), (''ECD_C_win_t3in'', elnk),
      (''ECD_C_t3wlout_wlout'', elnk), (''ECD_C_t3out_din'', elnk),
      (''ECD_C_wlout_wlin'', elnk), (''ECD_C_vo_vi1'', elnk), 
      (''ECD_C_vi1_vi2'', elnk),
      (''E_WTSys_WT1'', elnk), (''E_WTSys_WT2'', elnk), 
      (''E_WTSys_C'', elnk), (''E_WT1_I'', elnk),
      (''E_WT1_P'', elnk), (''E_WT1_T1'', elnk), (''E_WT1_T2'', elnk),
      (''E_WT2_T3'', elnk), (''E_WT2_D'', elnk),
      (''E_I_iout'', elnk), (''E_P_pin'', elnk), 
      (''E_P_pout'', elnk), (''E_T1_t1in'', elnk), 
      (''E_T1_t1out'', elnk), (''E_T2_t2in'', elnk),
      (''E_T2_t2out'', elnk), (''E_T3_t3in'', elnk), 
      (''E_T3_t3wlout'', elnk), (''E_T3_vi2'', elnk),
      (''E_C_wlin'', elnk), (''E_C_vo'', elnk), (''E_D_din'', elnk),
      (''E_WT1_wout'', elnk), (''E_WT2_win'', elnk),
      (''E_WT2_wlout'', elnk), (''E_WT2_vi1'', elnk),
      (''E_C_iout_t1in_src'', elnk), 
      (''E_C_iout_t1in_tgt'', elnk),
      (''E_C_t1out_pin_src'', elnk), 
      (''E_C_t1out_pin_tgt'', elnk),
      (''E_C_pout_t2in_src'', elnk), 
      (''E_C_pout_t2in_tgt'', elnk),
      (''E_C_t2out_wout_src'', elnk), 
      (''E_C_t2out_wout_tgt'', elnk),
      (''E_C_wout_win_src'', elnk), 
      (''E_C_wout_win_tgt'', elnk), 
      (''E_C_win_t3in_src'', elnk),
      (''E_C_win_t3in_tgt'', elnk),
      (''E_C_t3wlout_wlout_src'', elnk), 
      (''E_C_t3wlout_wlout_tgt'', elnk),
      (''E_C_t3out_din_src'', elnk),
      (''E_C_t3out_din_tgt'', elnk),
      (''E_C_wlout_wlin_src'', elnk),
      (''E_C_wlout_wlin_tgt'', elnk),
      (''E_C_vo_vi1_src'', elnk),
      (''E_C_vo_vi1_tgt'', elnk),
      (''E_C_vi1_vi2_src'', elnk), 
      (''E_C_vi1_vi2_tgt'', elnk), 
      (''E_iout_ty'', elnk), 
      (''E_t1in_ty'', elnk), 
      (''E_t1out_ty'', elnk), 
      (''E_pin_ty'', elnk), 
      (''E_pout_ty'', elnk), 
      (''E_t2in_ty'', elnk),
      (''E_t2out_ty'', elnk), 
      (''E_wout_ty'', elnk),
      (''E_win_ty'', elnk), 
      (''E_wlout_ty'', elnk),
      (''E_vi1_ty'', elnk), 
      (''E_t3in_ty'', elnk), 
      (''E_t3wlout_ty'', elnk), (''E_t3out_ty'', elnk),
      (''E_vi2_ty'', elnk), (''E_din_ty'', elnk), 
      (''E_wlin_ty'', elnk), (''E_vo_ty'', elnk),
      (''ERPrTankIO'', eref), 
      (''ERPrTankIOV'', eref), (''ERPrInflow'', eref),
      (''ERPrPipe'', eref), (''ERPrDrain'', eref),
      (''ERPrWaterTanks1'', eref), (''ERPrWaterTanks2'', eref),
      (''ERPrController'', eref), 
      (''ERPrInflow_wout'', eref), 
      (''ERPrTankIO_win'', eref), (''ERPrTankIO_wout'', eref), 
      (''ERPrPipe_win'', eref), 
      (''ERPrPipe_wout'', eref), 
      (''ERPrWaterTanks1_wout'', eref), 
      (''ERPrWaterTanks2_win'', eref),
      (''ERPrWaterTanks2_wlout'', eref), 
      (''ERPrWaterTanks2_vi'', eref),
      (''ERPrController_wlin'', eref),
      (''ERPrController_vo'', eref),
      (''ERPrDrain_win'', eref), 
      (''ERPrTankIOV_win'', eref), 
      (''ERPrTankIOV_wout'', eref), 
      (''ERPrTankIOV_wlout'', eref),
      (''ERPrTankIOV_vi'', eref)],
      srcmG = [], 
      tgtmG = []\<rparr>"

axiomatization
where
  Es_SG_CD_3WTs: "Es (toSGr SG_CD_3WTsP) \<subseteq> E_A"
  and Ns_SG_CD_3WTs: "Ns (toSGr SG_CD_3WTsP) \<subseteq> V_A"

value "consInh SG_CD_3WTsP"

lemma wf_SG_CD_3WTsP: "is_wf_sg (toSGr SG_CD_3WTsP)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_CD_3WTsP)"
    proof (simp add: is_wf_g_def, rule conjI)
      show "Ns (toSGr SG_CD_3WTsP) \<subseteq> V_A"
      using Ns_SG_CD_3WTs by (simp add: SG_CD_3WTsP_def)
    next
      apply_end(rule conjI)
      show "Es (toSGr SG_CD_3WTsP) \<subseteq> E_A"
      using Es_SG_CD_3WTs by (simp add: SG_CD_3WTsP_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (src (toSGr SG_CD_3WTsP)) (Es (toSGr SG_CD_3WTsP)) (Ns (toSGr SG_CD_3WTsP))"
      by (auto simp add: ftotal_on_def SG_CD_3WTsP_def toSGr_def)
    next
      show "ftotal_on (tgt (toSGr SG_CD_3WTsP)) (Es (toSGr SG_CD_3WTsP)) (Ns (toSGr SG_CD_3WTsP))"
      by (simp add: ftotal_on_def, rule conjI, simp add: SG_CD_3WTsP_def toSGr_def)
        (rule subsetI, auto simp add: SG_CD_3WTsP_def toSGr_def)
    qed      
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_CD_3WTsP)"
        using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_CD_3WTsP)) (Ns (toSGr SG_CD_3WTsP)) SGNTy_set"
        by (simp add: ftotal_on_def SGNTy_set_def SG_CD_3WTsP_def toSGr_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (ety (toSGr SG_CD_3WTsP)) (Es (toSGr SG_CD_3WTsP)) SGETy_set"
        by (simp add: ftotal_on_def, rule conjI, rule equalityI)
        (simp_all add: SGNTy_set_def SG_CD_3WTsP_def toSGr_def SGETy_set_def)
    next
      apply_end(rule conjI) 
      show "dom (srcm (toSGr SG_CD_3WTsP)) = EsTy (toSGr SG_CD_3WTsP) {Some erelbi, Some ecompbi}"
        by (simp add: SG_CD_3WTsP_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI) 
      show "dom (tgtm (toSGr SG_CD_3WTsP)) = EsTy (toSGr SG_CD_3WTsP) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_CD_3WTsP_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_CD_3WTsP) \<subseteq> EsId (toSGr SG_CD_3WTsP)"
      proof
        fix x
        assume " x \<in> EsR (toSGr SG_CD_3WTsP)"
        then show "x \<in> EsId (toSGr SG_CD_3WTsP)"
        by (auto simp add: EsR_def toSGr_def EsTy_def vimage_def SG_CD_3WTsP_def EsId_def
          split: if_splits)
      qed
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_CD_3WTsP) ` EsTy (toSGr SG_CD_3WTsP) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (simp add: toSGr_def image_def SG_CD_3WTsP_def EsTy_def)
    next
      show "acyclicGr (inhG (toSGr SG_CD_3WTsP))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_CD' Fragment*)
definition F_CD_3WTsP :: "Fr_ls"
where
   "F_CD_3WTsP \<equiv> \<lparr>sg_ls = SG_CD_3WTsP, 
    tr_ls = [(''ERPrTankIO'', ''TankIO''), (''ERPrTankIOV'', ''TankIOV''), 
      (''ERPrInflow'', ''Inflow''), (''ERPrPipe'', ''Pipe''),
      (''ERPrDrain'', ''Drain''),
      (''ERPrWaterTanks1'', ''WaterTanks1''), (''ERPrWaterTanks2'', ''WaterTanks2''), 
      (''ERPrController'', ''Controller''),
      (''ERPrInflow_wout'', ''Inflow_wout''), 
      (''ERPrTankIO_win'', ''TankIO_win''), 
      (''ERPrTankIO_wout'', ''TankIO_wout''),
      (''ERPrPipe_win'', ''Pipe_win''),
      (''ERPrPipe_wout'', ''Pipe_wout''),
      (''ERPrWaterTanks1_wout'', ''WaterTanks1_wout''),
      (''ERPrWaterTanks2_win'', ''WaterTanks2_win''),
      (''ERPrWaterTanks2_wlout'', ''WaterTanks2_wlout''),
      (''ERPrWaterTanks2_vi'', ''WaterTanks2_vi''),
      (''ERPrController_wlin'', ''Controller_wlin''),
      (''ERPrController_vo'', ''Controller_vo''),
      (''ERPrDrain_win'', ''Drain_win''),
      (''ERPrTankIOV_win'', ''TankIOV_win''),
      (''ERPrTankIOV_wout'', ''TankIOV_wout''),
      (''ERPrTankIOV_wlout'', ''TankIOV_wlout''),
      (''ERPrTankIOV_vi'', ''TankIOV_vi'')]\<rparr>"

value "consRefs F_CD_3WTsP"

value "consUFs [F_ASD_3WTsP, F_CD_3WTsP]"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_CD_3WTs: "is_wf_fr (toFr F_CD_3WTsP)"
  proof -
    let ?refs_F_CD_3WTsP = "{(''PrTankIO'', ''TankIO''), 
      (''PrTankIOV'', ''TankIOV''), (''PrInflow'', ''Inflow''),
      (''PrPipe'', ''Pipe''), (''PrDrain'', ''Drain''), 
      (''PrWaterTanks1'', ''WaterTanks1''),
      (''PrWaterTanks2'', ''WaterTanks2''), 
      (''PrController'', ''Controller''),
      (''PrInflow_wout'', ''Inflow_wout''), 
      (''PrTankIO_win'', ''TankIO_win''),
      (''PrTankIO_wout'', ''TankIO_wout''), 
      (''PrPipe_win'', ''Pipe_win''),
      (''PrPipe_wout'', ''Pipe_wout''), 
      (''PrWaterTanks1_wout'', ''WaterTanks1_wout''),
      (''PrWaterTanks2_win'', ''WaterTanks2_win''), 
      (''PrWaterTanks2_wlout'', ''WaterTanks2_wlout''),
      (''PrWaterTanks2_vi'', ''WaterTanks2_vi''), 
      (''PrController_wlin'', ''Controller_wlin''),
      (''PrController_vo'', ''Controller_vo''), 
      (''PrDrain_win'', ''Drain_win''),
      (''PrTankIOV_win'', ''TankIOV_win''), (''PrTankIOV_wout'', ''TankIOV_wout''),
      (''PrTankIOV_wlout'', ''TankIOV_wlout''), (''PrTankIOV_vi'', ''TankIOV_vi'')}"
    have h_EsRP: "EsRP (sg (toFr F_CD_3WTsP)) = {''ERPrTankIO'', ''ERPrTankIOV'', 
      ''ERPrInflow'', ''ERPrPipe'', ''ERPrDrain'', ''ERPrWaterTanks1'', 
      ''ERPrWaterTanks2'', ''ERPrController'', ''ERPrInflow_wout'', 
      ''ERPrTankIO_win'', ''ERPrTankIO_wout'',
      ''ERPrPipe_win'', ''ERPrPipe_wout'',
      ''ERPrWaterTanks1_wout'', ''ERPrWaterTanks2_win'',
      ''ERPrWaterTanks2_wlout'', ''ERPrWaterTanks2_vi'',
      ''ERPrController_wlin'', ''ERPrController_vo'',
      ''ERPrDrain_win'', ''ERPrTankIOV_win'',
      ''ERPrTankIOV_wout'', ''ERPrTankIOV_wlout'', ''ERPrTankIOV_vi''}"
      by (rule equalityI, rule subsetI, simp_all add: EsRP_def EsR_def EsTy_def NsP_def NsTy_def 
        toFr_def F_CD_3WTsP_def toSGr_def SG_CD_3WTsP_def split: if_splits)
    have h_ftotal_tr: "ftotal_on (tr (toFr F_CD_3WTsP)) (EsRP (sg (toFr F_CD_3WTsP))) V_A"
      using Ns_SG_ASD_3WTsP
      by (simp add: h_EsRP)(simp add: F_CD_3WTsP_def SG_CD_3WTsP_def toSGr_def toFr_def  
          ftotal_on_def SG_ASD_3WTsP_def) 
    from wf_SG_CD_3WTsP have hb: "is_wf_sg (sg (toFr F_CD_3WTsP))"
      by (simp add: toFr_def F_CD_3WTsP_def)
    have refs_F_CD_3WTsP: "refs (toFr F_CD_3WTsP) = ?refs_F_CD_3WTsP"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    have h_NsP: "NsP (sg (toFr F_CD_3WTsP)) = 
      {''PrTankIO'', ''PrTankIOV'', ''PrInflow'',
      ''PrPipe'', ''PrDrain'', ''PrWaterTanks1'',
      ''PrWaterTanks2'', ''PrController'',
      ''PrInflow_wout'', ''PrTankIO_win'',
      ''PrTankIO_wout'', ''PrPipe_win'', ''PrPipe_wout'', 
      ''PrWaterTanks1_wout'', ''PrWaterTanks2_win'', 
      ''PrWaterTanks2_wlout'', ''PrWaterTanks2_vi'', 
      ''PrController_wlin'', ''PrController_vo'', 
      ''PrDrain_win'', ''PrTankIOV_win'', ''PrTankIOV_wout'',
      ''PrTankIOV_wlout'', ''PrTankIOV_vi''}"
      by (rule equalityI, rule subsetI, simp_all add: F_CD_3WTsP_def NsP_def NsTy_def 
        toFr_def SG_CD_3WTsP_def toSGr_def vimage_def split: if_splits)
    show ?thesis
    proof (simp add: is_wf_fr_def)
      apply_end(rule conjI)
      show "is_wf_sg (sg (toFr F_CD_3WTsP))"  
        by (simp add: wf_SG_CD_3WTsP toFr_def F_CD_3WTsP_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (tr (toFr F_CD_3WTsP)) (EsRP (sg (toFr F_CD_3WTsP))) V_A"
        by (simp add: h_ftotal_tr)
    next
      apply_end(rule conjI)  
      show "inj_on (src (sg (toFr F_CD_3WTsP))) (EsRP (sg (toFr F_CD_3WTsP)))"
      proof (simp add: inj_on_def, clarify)
        fix x y
        assume h1: "x \<in> EsRP (sg (toFr F_CD_3WTsP))"
          and h2: "y \<in> EsRP (sg (toFr F_CD_3WTsP))"
          and h3: "src (sg (toFr F_CD_3WTsP)) x = src (sg (toFr F_CD_3WTsP)) y"
        show "x = y"
        proof (case_tac  "y = ''ERPrTankIO''")
          assume "y = ''ERPrTankIO''"
          then show "x = y"
          using h1 h2 h3 by (simp add: h_EsRP)(simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
            SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
        next
          assume h4: "y \<noteq> ''ERPrTankIO''" 
          then show "x = y"
          proof (case_tac  "y = ''ERPrTankIOV''")
            assume "y = ''ERPrTankIOV''"
            then show "x = y"
            using h1 h2 h3 by (simp add: h_EsRP)(simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
              SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
          next
            assume h5: "y \<noteq> ''ERPrTankIOV''"
            then show "x = y"
            proof (case_tac  "y = ''ERPrInflow''")
              assume "y = ''ERPrInflow''"
              then show "x = y"
              using h1 h2 h3 by (simp add: h_EsRP)(simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
            next
              assume h6: "y \<noteq> ''ERPrInflow''"
              then show "x = y"
              proof (case_tac  "y = ''ERPrPipe''")
                assume "y = ''ERPrPipe''"
                then show "x = y"
                using h1 h2 h3 by (simp add: h_EsRP)(simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                  SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
              next
                assume h7: "y \<noteq> ''ERPrPipe''"
                then show "x = y"
                proof (case_tac "y = ''ERPrDrain''")
                  assume "y = ''ERPrDrain''"
                  then show "x = y"
                  using h1 h2 h3 by (simp add: h_EsRP)(simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                    SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                next
                  assume h8: "y \<noteq> ''ERPrDrain''"
                  then show "x = y"
                  proof (case_tac "y = ''ERPrWaterTanks1''")
                    assume "y = ''ERPrWaterTanks1''"
                    then show "x = y"
                    using h1 h2 h3 by (simp add: h_EsRP)
                      (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                      SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                  next
                    assume h9: "y \<noteq> ''ERPrWaterTanks1''"
                    then show "x = y"
                    proof (case_tac "y = ''ERPrWaterTanks2''")
                      assume "y = ''ERPrWaterTanks2''"
                      then show "x = y"
                      using h1 h2 h3 by (simp add: h_EsRP)
                        (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                        SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                    next
                      assume h10: "y \<noteq> ''ERPrWaterTanks2''"
                      then show "x = y"
                      proof (case_tac "y = ''ERPrController''")
                        assume "y = ''ERPrController''"
                        then show "x = y"
                        using h1 h2 h3 by (simp add: h_EsRP)
                          (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                            SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                      next
                        assume h11: "y \<noteq> ''ERPrController''"
                        then show "x = y"
                        proof (case_tac "y = ''ERPrInflow_wout''")
                          assume "y = ''ERPrInflow_wout''"
                          then show "x = y"
                          using h1 h2 h3 by (simp add: h_EsRP)
                            (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                              SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                        next
                          assume h12: "y \<noteq> ''ERPrInflow_wout''"
                          then show "x = y"
                          proof (case_tac "y = ''ERPrTankIO_win''")
                            assume "y = ''ERPrTankIO_win''"
                            then show "x = y"
                            using h1 h2 h3 by (simp add: h_EsRP)
                              (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                              SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                          next
                            assume h13: "y \<noteq> ''ERPrTankIO_win''"
                            then show "x = y"
                            proof (case_tac "y = ''ERPrTankIO_wout''")
                              assume "y = ''ERPrTankIO_wout''"
                              then show "x = y"
                                using h1 h2 h3 by (simp add: h_EsRP)
                                (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                  SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                            next
                              assume h14: "y \<noteq> ''ERPrTankIO_wout''"
                              then show "x = y"
                              proof (case_tac "y = ''ERPrPipe_win''")
                                assume "y = ''ERPrPipe_win''"
                                then show "x = y"
                                using h1 h2 h3 by (simp add: h_EsRP)
                                  (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                    SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                              next
                                assume h15: "y \<noteq> ''ERPrPipe_win''"
                                then show "x = y"
                                proof (case_tac "y = ''ERPrPipe_wout''")
                                  assume "y = ''ERPrPipe_wout''"
                                  then show "x = y"
                                  using h1 h2 h3 by (simp add: h_EsRP)
                                    (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                    SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                next
                                  assume h16: "y \<noteq> ''ERPrPipe_wout''"
                                  then show "x = y"
                                  proof (case_tac "y = ''ERPrWaterTanks1_wout''")
                                    assume "y = ''ERPrWaterTanks1_wout''"
                                    then show "x = y"
                                    using h1 h2 h3 by (simp add: h_EsRP)
                                      (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                        SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                  next
                                    assume h17: "y \<noteq> ''ERPrWaterTanks1_wout''"
                                    then show "x = y"
                                    proof (case_tac "y = ''ERPrWaterTanks2_win''")
                                      assume "y = ''ERPrWaterTanks2_win''"
                                      then show "x = y"
                                      using h1 h2 h3 by (simp add: h_EsRP)
                                      (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                        SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                    next
                                      assume h18: "y \<noteq> ''ERPrWaterTanks2_win''"
                                      then show "x = y"
                                      proof (case_tac "y = ''ERPrWaterTanks2_wlout''")
                                        assume "y = ''ERPrWaterTanks2_wlout''"
                                        then show "x = y"
                                        using h1 h2 h3 by (simp add: h_EsRP)
                                        (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                          SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                      next
                                        assume h19: "y \<noteq> ''ERPrWaterTanks2_wlout''"
                                        then show "x = y"
                                        proof (case_tac "y=''ERPrWaterTanks2_vi''")
                                          assume "y=''ERPrWaterTanks2_vi''"
                                          then show "x = y"
                                          using h1 h2 h3 by (simp add: h_EsRP)
                                          (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                            SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                        next
                                          assume h20: "y \<noteq> ''ERPrWaterTanks2_vi''"
                                          then show "x = y"
                                          proof (case_tac "y=''ERPrController_wlin''")
                                            assume "y=''ERPrController_wlin''"
                                            then show "x = y"
                                            using h1 h2 h3 by (simp add: h_EsRP)
                                            (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                            SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                          next
                                            assume h21: "y\<noteq>''ERPrController_wlin''" 
                                            then show "x = y"
                                            proof (case_tac "y=''ERPrController_vo''")
                                              assume "y = ''ERPrController_vo''"
                                              then show "x = y"
                                              using h1 h2 h3 by (simp add: h_EsRP)
                                              (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                                  SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                            next
                                              assume h22: "y \<noteq> ''ERPrController_vo''"
                                              then show "x = y"
                                              proof (case_tac "y = ''ERPrDrain_win''")
                                                assume "y = ''ERPrDrain_win''"
                                                then show "x = y"
                                                using h1 h2 h3 by (simp add: h_EsRP)
                                                (simp add: F_CD_3WTsP_def EsRP_def EsR_def EsTy_def
                                                  SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                              next
                                                assume h23: "y \<noteq> ''ERPrDrain_win''"
                                                then show "x = y"
                                                proof (case_tac "y = ''ERPrTankIOV_win''")
                                                  assume "y = ''ERPrTankIOV_win''"
                                                  then show "x = y"
                                                  using h1 h2 h3 by (simp add: h_EsRP)
                                                  (simp add: F_CD_3WTsP_def EsRP_def EsR_def 
                                                    EsTy_def
                                                  SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                                next
                                                  assume h24: "y \<noteq> ''ERPrTankIOV_win''"
                                                  then show "x = y"
                                                  proof (case_tac "y = ''ERPrTankIOV_wout''")
                                                    assume "y = ''ERPrTankIOV_wout''"
                                                    then show "x = y"
                                                    using h1 h2 h3 by (simp add: h_EsRP)
                                                    (simp add: F_CD_3WTsP_def EsRP_def EsR_def 
                                                    EsTy_def
                                                    SG_CD_3WTsP_def toFr_def toSGr_def split: if_splits)
                                                  next
                                                    assume h25: "y \<noteq> ''ERPrTankIOV_wout''"
                                                    then show "x = y"
                                                    proof (case_tac "y = ''ERPrTankIOV_wlout''")
                                                      assume "y = ''ERPrTankIOV_wlout''"
                                                      then show "x = y"
                                                      using h1 h2 h3 by (simp add: h_EsRP)
                                                      (simp add: F_CD_3WTsP_def EsRP_def EsR_def 
                                                        EsTy_def
                                                        SG_CD_3WTsP_def toFr_def 
                                                        toSGr_def split: if_splits)
                                                    next
                                                      assume h26: "y \<noteq> ''ERPrTankIOV_wlout''"
                                                      then show "x = y"
                                                      proof (case_tac "y = ''ERPrTankIOV_vi''")
                                                        assume "y = ''ERPrTankIOV_vi''"
                                                        then show "x = y"
                                                        using h1 h2 h3 by (simp add: h_EsRP)
                                                        (simp add: F_CD_3WTsP_def EsRP_def EsR_def 
                                                          EsTy_def SG_CD_3WTsP_def toFr_def 
                                                          toSGr_def split: if_splits)
                                                      next  
                                                        assume "y \<noteq> ''ERPrTankIOV_vi''"
                                                        then show "x = y"
                                                        using h1 h2 h4 h5 h6 h7 h8 h9 h10 h11 h12
                                                        h13 h14 h15 h16 h17 h18 h19 h20 h21 
                                                        h22 h23 h24 h25 h26 
                                                        by (simp add: h_EsRP)
                                                      qed
                                                    qed
                                                  qed
                                                qed
                                              qed
                                            qed
                                          qed
                                        qed
                                      qed
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    next
      apply_end(rule conjI)  
      show "ran (src (sg (toFr F_CD_3WTsP)) |` EsRP (sg (toFr F_CD_3WTsP))) = NsP (sg (toFr F_CD_3WTsP))"
      by (simp add: h_EsRP h_NsP)(rule equalityI, simp_all add: F_CD_3WTsP_def SG_CD_3WTsP_def  
        toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_CD_3WTsP)) \<longrightarrow> nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume h1: "v \<in> NsP (sg (toFr F_CD_3WTsP))"
        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
        proof (case_tac  "v = ''PrTankIO''")
          assume "v = ''PrTankIO''"
          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
            by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
        next  
          assume h2: "v \<noteq> ''PrTankIO''"
          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
          proof (case_tac  "v = ''PrTankIOV''")
            assume "v = ''PrTankIOV''"
            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
          next
            assume h3: "v \<noteq> ''PrTankIOV''"
            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
            proof (case_tac  "v = ''PrPipe''")
              assume "v = ''PrPipe''"
              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
            next
              assume h4: "v \<noteq> ''PrPipe''"
              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
              proof (case_tac  "v = ''PrDrain''")
                assume "v = ''PrDrain''"
                then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                  by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
              next
                assume h5: "v \<noteq> ''PrDrain''"
                then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                proof (case_tac  "v = ''PrWaterTanks1''")
                  assume "v = ''PrWaterTanks1''"
                  then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                    by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
                next
                  assume h6: "v \<noteq> ''PrWaterTanks1''"
                  then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                  proof (case_tac "v = ''PrWaterTanks2''")
                    assume "v = ''PrWaterTanks2''"
                    then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                      by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
                  next
                    assume h7: "v \<noteq> ''PrWaterTanks2''"
                    then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                    proof (case_tac "v = ''PrController_wlin''")
                      assume "v = ''PrController_wlin''"
                      then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                        by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
                    next
                      assume h8: "v \<noteq> ''PrController_wlin''"
                      then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                      proof (case_tac "v = ''PrInflow_wout''")
                        assume "v = ''PrInflow_wout''"
                        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                          by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
                      next
                        assume h9: "v \<noteq> ''PrInflow_wout''"
                        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                        proof (case_tac "v = ''PrTankIO_win''")
                          assume "v = ''PrTankIO_win''"
                          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                            by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP trancl_in)
                        next
                          assume h10: "v \<noteq> ''PrTankIO_win''"
                          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                          proof (case_tac "v = ''PrController_wlin''")
                            assume "v = ''PrController_wlin''"
                            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                trancl_in)
                          next
                            assume h11: "v \<noteq> ''PrController_wlin''"
                            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                            proof (case_tac "v = ''PrController_vo''")
                              assume "v = ''PrController_vo''"
                              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                trancl_in)
                            next
                              assume h12: "v \<noteq> ''PrController_vo''"
                              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                              proof (case_tac "v = ''PrDrain_win''")
                                assume "v = ''PrDrain_win''"
                                then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                  trancl_in)
                              next
                                assume h13: "v \<noteq> ''PrDrain_win''"
                                then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                proof (case_tac "v = ''PrTankIOV_win''")
                                  assume "v = ''PrTankIOV_win''"
                                  then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                    by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                  trancl_in)
                                next
                                  assume h14: "v \<noteq> ''PrTankIOV_win''"
                                  then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                  proof (case_tac "v = ''PrTankIOV_wout''")
                                    assume "v = ''PrTankIOV_wout''"
                                    then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                    by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                      trancl_in)
                                  next
                                    assume h15: "v \<noteq> ''PrTankIOV_wout''"
                                    then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                    proof (case_tac "v = ''PrTankIOV_wlout''")
                                      assume "v = ''PrTankIOV_wlout''"
                                      then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                      by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                        trancl_in)
                                    next
                                      assume h16: "v \<noteq> ''PrTankIOV_wlout''"
                                      then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                      proof (case_tac "v = ''PrTankIOV_vi''")
                                        assume "v = ''PrTankIOV_vi''"
                                        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                        by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                        trancl_in)
                                      next
                                        assume "v \<noteq> ''PrTankIOV_vi''"
                                        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                        proof (case_tac "v = ''PrInflow''")
                                          assume "v = ''PrInflow''"
                                          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                          by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                            trancl_in)
                                        next
                                          assume h17: "v \<noteq> ''PrInflow''"
                                          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                          proof (case_tac "v = ''PrController''")
                                            assume "v = ''PrController''"
                                            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                            by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                              trancl_in)
                                          next
                                            assume h18: "v \<noteq>''PrController''"
                                            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                            proof (case_tac "v = ''PrTankIO_wout''")
                                              assume "v = ''PrTankIO_wout''"
                                              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                trancl_in)
                                            next
                                              assume h19: "v \<noteq> ''PrTankIO_wout''"
                                              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                              proof (case_tac "v = ''PrPipe_win''")
                                                assume "v = ''PrPipe_win''"
                                                then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                  trancl_in)
                                              next
                                                assume h20: "v \<noteq> ''PrPipe_win''"
                                                then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                proof (case_tac "v = ''PrPipe_wout''")
                                                  assume "v = ''PrPipe_wout''"
                                                  then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                  by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                  trancl_in)
                                                next
                                                  assume h21: "v \<noteq> ''PrPipe_wout''"
                                                  then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                  proof (case_tac "v = ''PrWaterTanks1_wout''")
                                                    assume "v = ''PrWaterTanks1_wout''"
                                                    then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                    by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                      trancl_in)
                                                  next
                                                    assume h22: "v \<noteq> ''PrWaterTanks1_wout''"
                                                    then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                    proof (case_tac "v = ''PrWaterTanks1_wout''")
                                                      assume "v = ''PrWaterTanks1_wout''"
                                                      then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                      by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                      trancl_in)
                                                    next
                                                      assume h23: "v \<noteq> ''PrWaterTanks1_wout''"
                                                      then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                      proof (case_tac "v = ''PrWaterTanks2_win''")
                                                        assume "v = ''PrWaterTanks2_win''"
                                                        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                        by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                          trancl_in)
                                                      next
                                                        assume h24: "v \<noteq> ''PrWaterTanks2_win''"
                                                        then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                        proof (case_tac "v = ''PrWaterTanks2_wlout''")
                                                          assume "v = ''PrWaterTanks2_wlout''"
                                                          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                          by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                            trancl_in)
                                                        next
                                                          assume h25: "v \<noteq> ''PrWaterTanks2_wlout''"
                                                          then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                          proof (case_tac "v = ''PrWaterTanks2_vi''")
                                                            assume "v = ''PrWaterTanks2_vi''"
                                                            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                                trancl_in)
                                                          next
                                                            assume h26: "v \<noteq> ''PrWaterTanks2_vi''"
                                                            then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                            proof (case_tac "v = ''PrTankIOV_vi''")
                                                              assume "v = ''PrTankIOV_vi''"
                                                              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                                by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTsP 
                                                                trancl_in)
                                                            next
                                                              assume h27: "v \<noteq> ''PrTankIOV_vi''"
                                                              then show "nonPRefsOf (toFr F_CD_3WTsP) v \<noteq> {}"
                                                              using h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
                                                              h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
                                                              h27 by (simp add: h_NsP)
                                                            qed
                                                          qed
                                                        qed
                                                      qed
                                                    qed
                                                  qed
                                                qed
                                              qed
                                            qed
                                          qed
                                        qed
                                      qed
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      have h_wf_g: "is_wf_g (toSGr SG_CD_3WTsP)"
        using wf_SG_CD_3WTsP
        by (simp add: is_wf_sg_def)
      show "acyclic_fr (toFr F_CD_3WTsP)"
      proof -
          from wf_SG_CD_3WTsP have "acyclic (inh (sg (toFr F_CD_3WTsP)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_CD_3WTsP_def toFr_def)
          then show "acyclic_fr (toFr F_CD_3WTsP)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_CD_3WTsP)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_CD_3WTsP)))"
              using wf_SG_CD_3WTsP by (simp add: F_CD_3WTsP_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_CD_3WTsP))) \<inter> Domain (refs (toFr F_CD_3WTsP)) = {}"
              using h2 
                by (simp add: refs_F_CD_3WTsP)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_CD_3WTsP)) \<inter> Domain (inh (sg (toFr F_CD_3WTsP))) = {}"
              using h2 by (simp add: refs_F_CD_3WTsP)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_CD_3WTsP))"
              by (simp add: refs_F_CD_3WTsP)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_CD_3WTsP)) \<union> refs (toFr F_CD_3WTsP))"
              by (simp add: acyclic_Un)
          qed
        qed
    next
      show "proxies_dont_inherit (toFr F_CD_3WTsP)"
      proof (simp add: proxies_dont_inherit_def, rule equalityI, rule subsetI)
        fix x
        assume "x \<in> ran (src (sg (toFr F_CD_3WTsP)) |` EsI (sg (toFr F_CD_3WTsP))) \<inter>
             NsP (sg (toFr F_CD_3WTsP))"
        then show "x \<in> {}"
        by (simp add: h_NsP)(auto simp add: restrict_map_def 
          F_CD_3WTsP_def toFr_def vimage_def SG_CD_3WTsP_def toSGr_def EsI_def EsTy_def ran_def
          split: if_splits)
      next
        show "{} \<subseteq> ran (src (sg (toFr F_CD_3WTsP)) |` EsI (sg (toFr F_CD_3WTsP))) \<inter> NsP (sg (toFr F_CD_3WTsP))"
        by (simp)
      qed
    qed
  qed

(*Define the other morphism*)
definition T_F_CD_3WTsP :: "MorphL"
where
   "T_F_CD_3WTsP \<equiv> \<lparr>fVL = [
    (''PrTankIO'', ''PrBlock3''), (''PrTankIOV'', ''PrBlock3''), 
    (''PrInflow'', ''PrBlock3''), (''PrPipe'', ''PrBlock3''), 
    (''PrDrain'', ''PrBlock3''), (''PrWaterTanks1'', ''PrBlock3''), 
    (''PrWaterTanks2'', ''PrBlock3''), (''PrController'', ''PrBlock3''), 
    (''CD_3WTs'', ''ConnectionsDiagram''), (''WTSys'', ''BlockInstance''), 
    (''I'', ''BlockInstance''), (''P'', ''BlockInstance''), (''T1'', ''BlockInstance''), 
    (''T2'', ''BlockInstance''), (''T3'', ''BlockInstance''),  
    (''C'', ''BlockInstance''), (''D'', ''BlockInstance''), 
    (''WT1'', ''BlockInstance''), (''WT2'', ''BlockInstance''),
    (''iout'', ''Port''), (''t1in'', ''Port''), (''t1out'', ''Port''),
    (''pin'', ''Port''), (''pout'', ''Port''), (''t2in'', ''Port''),
    (''t2out'', ''Port''), (''wout'', ''Port''), (''win'', ''Port''),
    (''wlout'', ''Port''), (''vi1'', ''Port''), (''t3in'', ''Port''),
    (''t3wlout'', ''Port''), (''t3out'', ''Port''), (''vi2'', ''Port''),
    (''din'', ''Port''), (''din'', ''Port''), (''wlin'', ''Port''), 
    (''vo'', ''Port''), 
    (''C_iout_t1in'', ''Connector''), (''C_t1out_pin'', ''Connector''), 
    (''C_pout_t2in2'', ''Connector''), (''C_t2out_wout'', ''Connector''), 
    (''C_wout_win'', ''Connector''),  (''C_win_t3in'', ''Connector''), 
    (''C_t3wlout_wlout'', ''Connector''), (''C_t3out_din'', ''Connector''), 
    (''C_wlout_wlin'', ''Connector''), (''C_vo_vi1'', ''Connector''), 
    (''C_vi1_vi2'', ''Connector''), (''PrInflow_wout'', ''PrFlowPort2''), 
    (''PrTankIO_win'', ''PrFlowPort2''), (''PrTankIO_wout'', ''PrFlowPort2''), 
    (''PrPipe_win'', ''PrFlowPort2''), (''PrPipe_wout'', ''PrFlowPort2''), 
    (''PrWaterTanks1_wout'', ''PrFlowPort2''), (''PrWaterTanks2_win'', ''PrFlowPort2''),
    (''PrWaterTanks2_wlout'', ''PrFlowPort2''), (''PrWaterTanks2_vi'', ''PrFlowPort2''),
    (''PrController_wlin'', ''PrFlowPort2''), (''PrController_vo'', ''PrFlowPort2''),
    (''PrDrain_win'', ''PrFlowPort2''), (''PrTankIOV_win'', ''PrFlowPort2''),
    (''PrTankIOV_wout'', ''PrFlowPort2''), (''PrTankIOV_wlout'', ''PrFlowPort2''),
    (''PrTankIOV_vi'', ''PrFlowPort2'')],
    fEL = [(''ECD_WTSys'', ''ECDblocks''),
      (''ECD_I'', ''ECDblocks''), (''ECD_P'', ''ECDblocks''),
      (''ECD_T1'', ''ECDblocks''), (''ECD_T2'',  ''ECDblocks''),
      (''ECD_T3'', ''ECDblocks''), (''ECD_C'', ''ECDblocks''), 
      (''ECD_D'', ''ECDblocks''), (''ECD_WT1'', ''ECDblocks''), 
      (''ECD_WT2'', ''ECDblocks''), (''ECD_C_iout_t1in'', ''ECDconnectors''),
      (''ECD_C_t1out_pin'', ''ECDconnectors''), (''ECD_C_pout_t2in2'', ''ECDconnectors''),
      (''ECD_C_t2out_wout'', ''ECDconnectors''), (''ECD_C_wout_win'', ''ECDconnectors''),
      (''ECD_C_win_t3in'', ''ECDconnectors''), (''ECD_C_t3wlout_wlout'', ''ECDconnectors''),
      (''ECD_C_t3out_din'', ''ECDconnectors''), (''ECD_C_wlout_wlin'', ''ECDconnectors''),
      (''ECD_C_vo_vi1'', ''ECDconnectors''), (''ECD_C_vi1_vi2'', ''ECDconnectors''),
      (''E_WTSys_WT1'', ''EBIInside''), (''E_WTSys_WT2'', ''EBIInside''),
      (''E_WTSys_C'', ''EBIInside''), (''E_WT1_I'', ''EBIInside''),
      (''E_WT1_P'', ''EBIInside''), (''E_WT1_T1'', ''EBIInside''), 
      (''E_WT1_T2'', ''EBIInside''), (''E_WT2_T3'', ''EBIInside''),
      (''E_WT2_D'', ''EBIInside''), (''E_I_iout'', ''EBIports''), 
      (''E_P_pin'', ''EBIports''), (''E_P_pout'', ''EBIports''), 
      (''E_T1_t1in'', ''EBIports''), (''E_T1_t1out'', ''EBIports''),
      (''E_T2_t2in'', ''EBIports''), (''E_T2_t2out'', ''EBIports''),
      (''E_T3_t3in'', ''EBIports''), (''E_T3_t3wlout'', ''EBIports''),
      (''E_T3_vi2'', ''EBIports''), (''E_C_wlin'', ''EBIports''),
      (''E_C_vo'', ''EBIports''), (''E_D_din'', ''EBIports''),
      (''E_WT1_wout'', ''EBIports''), (''E_WT2_win'', ''EBIports''),
      (''E_WT2_wlout'', ''EBIports''), (''E_WT2_vi1'', ''EBIports''),
      (''E_C_iout_t1in_src'', ''EC_src''), (''E_C_iout_t1in_tgt'', ''EC_tgt''),
      (''E_C_t1out_pin_src'', ''EC_src''), (''E_C_t1out_pin_tgt'', ''EC_tgt''),
      (''E_C_pout_t2in_src'', ''EC_src''), (''E_C_pout_t2in_tgt'', ''EC_tgt''),
      (''E_C_t2out_wout_src'', ''EC_src''), (''E_C_t2out_wout_tgt'', ''EC_tgt''),
      (''E_C_wout_win_src'', ''EC_src''), (''E_C_wout_win_tgt'', ''EC_tgt''),
      (''E_C_win_t3in_src'', ''EC_src''), (''E_C_win_t3in_tgt'', ''EC_tgt''),
      (''E_C_t3wlout_wlout_src'', ''EC_src''), (''E_C_t3wlout_wlout_tgt'', ''EC_tgt''),
      (''E_C_t3out_din_src'', ''EC_src''), (''E_C_t3out_din_tgt'', ''EC_tgt''),
      (''E_C_wlout_wlin_src'', ''EC_src''), (''E_C_wlout_wlin_tgt'', ''EC_tgt''),
      (''E_C_vo_vi1_src'', ''EC_src''),  (''E_C_vo_vi1_tgt'', ''EC_tgt''),
      (''E_C_vi1_vi2_src'', ''EC_src''), (''E_C_vi1_vi2_tgt'', ''EC_tgt''),
      (''E_iout_ty'', ''EPortType''), (''E_t1in_ty'', ''EPortType''), 
      (''E_t1out_ty'', ''EPortType''), (''E_pin_ty'', ''EPortType''), 
      (''E_pout_ty'', ''EPortType''), (''E_t2in_ty'', ''EPortType''),
      (''E_t2out_ty'', ''EPortType''), (''E_wout_ty'', ''EPortType''), 
      (''E_win_ty'', ''EPortType''), (''E_wlout_ty'', ''EPortType''),
      (''E_vi1_ty'', ''EPortType''), (''E_t3in_ty'', ''EPortType''),
      (''E_t3wlout_ty'', ''EPortType''), (''E_t3out_ty'', ''EPortType''), 
      (''E_vi2_ty'', ''EPortType''), (''E_din_ty'', ''EPortType''), 
      (''E_wlin_ty'', ''EPortType''), (''E_vo_ty'', ''EPortType''),
      (''ERPrTankIO'', ''ERPrBlock3''), (''ERPrTankIOV'', ''ERPrBlock3''), 
      (''ERPrInflow'', ''ERPrBlock3''), (''ERPrPipe'', ''ERPrBlock3''),
      (''ERPrDrain'', ''ERPrBlock3''), (''ERPrWaterTanks1'', ''ERPrBlock3''),
      (''ERPrWaterTanks2'', ''ERPrBlock3''), (''ERPrController'', ''ERPrBlock3''),
      (''ERPrInflow_wout'', ''ERPrBlock3''), (''ERPrTankIO_win'', ''ERPrBlock3''),
      (''ERPrTankIO_wout'', ''ERPrBlock3''), (''ERPrPipe_win'', ''ERPrBlock3''),
      (''ERPrPipe_wout'', ''ERPrBlock3''), (''ERPrWaterTanks1_wout'', ''ERPrBlock3''),
      (''ERPrWaterTanks2_win'', ''ERPrBlock3''), (''ERPrWaterTanks2_wlout'', ''ERPrBlock3''),
      (''ERPrWaterTanks2_vi'', ''ERPrBlock3''),(''ERPrController_wlin'', ''ERPrBlock3''),
      (''ERPrController_vo'', ''ERPrBlock3''), (''ERPrDrain_win'', ''ERPrBlock3''),
      (''ERPrTankIOV_win'', ''ERPrBlock3''), (''ERPrTankIOV_wout'', ''ERPrBlock3''),
      (''ERPrTankIOV_wlout'', ''ERPrBlock3''), (''ERPrTankIOV_vi'', ''ERPrBlock3'')]\<rparr>"

end