theory Imp_Thms

imports  MMU_ARM_Refine_No_Fault

begin    


thm mmu_translate_non_det_det_refine
    mmu_translate_det_sat_no_flt_refine
    mmu_translate_sat_no_flt_refine
    mmu_translate_sat_no_flt_abs_refine
    mmu_write_det_sat_refine
    mmu_write_non_det_sat_refine
    write_refinement_saturated_incon_only


end
