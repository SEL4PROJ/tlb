theory  TLB_Op_Instants

imports 
  ARMv7_Mem_Write_Read_Ref

begin               



instantiation tlb_state_ext :: (type) reg_tlb_op   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_state_scheme \<Rightarrow> _))  = 
do {
    update_state (\<lambda>s. s\<lparr> tlb_set := tlb_set s - tlb_evict (typ_tlb s) \<rparr>);
    update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>)
  } "

thm update_TTBR0_tlb_state_ext_def
  definition   
  "(update_ASID a :: ('a tlb_state_scheme \<Rightarrow> _))  = 
do {
    update_state (\<lambda>s. s\<lparr> tlb_set := tlb_set s - tlb_evict (typ_tlb s) \<rparr>);
    update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>) 
}"                 
definition   
  "(Flush_TLB :: ('a tlb_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> tlb_set := {} \<rparr>)"

 definition   
  "(Flush_ASID a :: ('a tlb_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_set;
      update_state (\<lambda>s. s\<lparr> tlb_set := tlb - {e\<in>tlb. asid_entry e = a} - tlb_evict (typ_tlb s) \<rparr>)}"

 definition   
  "(Flush_varange vset :: ('a tlb_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_set;
      update_state (\<lambda>s. s\<lparr> tlb_set := tlb - \<Union>((\<lambda> v. {e\<in>tlb. v \<in> entry_range e}) ` vset) - 
                                             tlb_evict (typ_tlb s) \<rparr>)}"

definition   
  "(Flush_ASIDvarange a vset :: ('a tlb_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_set;
      update_state (\<lambda>s. s\<lparr> tlb_set := tlb -
                   (\<Union>v\<in> vset. {e \<in> tlb. (a,  v) \<in> entry_range_asid_tags e}) - 
                                             tlb_evict (typ_tlb s) \<rparr>)}"
  instance ..
end




instantiation tlb_det_state_ext :: (type) reg_tlb_op  
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>) "

thm update_TTBR0_tlb_det_state_ext_def

 definition   
  "(update_ASID a :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>) "

 definition   
  "(Flush_TLB  :: ('a tlb_det_state_scheme \<Rightarrow> _))  = update_state (\<lambda>s. s\<lparr> tlb_det_set := {} \<rparr>)"

definition   
  "(Flush_ASID a :: ('a tlb_det_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_det_set;
      update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb - {e\<in>tlb. asid_entry e = a} \<rparr>)}"

 definition   
  "(Flush_varange vset :: ('a tlb_det_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_det_set;
      update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb - \<Union>((\<lambda> v. {e\<in>tlb.   v \<in> entry_range e}) ` vset)\<rparr>)}"

definition   
  "(Flush_ASIDvarange a vset :: ('a tlb_det_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_det_set;
      update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb - 
          (\<Union>v\<in>vset. {e \<in> tlb. (a,   v) \<in> entry_range_asid_tags e})\<rparr>)}"
  instance ..
end


instantiation tlb_sat_no_flt_state_ext :: (type) reg_tlb_op   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      mem   <- read_state MEM;
      asid <- read_state ASID;
      let all_non_fault_entries = the ` {e\<in>pt_walk asid mem r ` UNIV. \<not>is_fault e};
      tlb0   <- read_state tlb_sat_no_flt_set;
      let tlb = tlb0 \<union> all_non_fault_entries; 
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>)} "

  thm update_TTBR0_tlb_sat_no_flt_state_ext_def

definition   
  "(update_ASID a :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>);
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      let all_non_fault_entries = the ` {e\<in>pt_walk a mem ttbr0 ` UNIV. \<not>is_fault e};
      tlb0   <- read_state tlb_sat_no_flt_set;
      let tlb = tlb0 \<union> all_non_fault_entries; 
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>)} "

definition   
  "(Flush_TLB :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
       update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := {} \<rparr>);
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := all_non_fault_entries \<rparr>)} "


 definition   
  "(Flush_ASID a :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_sat_no_flt_set;
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := (tlb - {e\<in>tlb. asid_entry e = a}) \<union> 
                                                       all_non_fault_entries \<rparr>)} "

definition   
  "(Flush_varange vset :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_sat_no_flt_set;
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := 
              (tlb - (\<Union>v\<in>vset. {e \<in> tlb.   v \<in> entry_range e})) \<union> all_non_fault_entries \<rparr>)} "

definition   
  "(Flush_ASIDvarange a vset :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))  = do {
      tlb   <- read_state tlb_sat_no_flt_set;
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid <- read_state ASID;
      let all_non_fault_entries = the ` {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
      update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := 
              (tlb - (\<Union>v\<in>vset. {e \<in> tlb. (a,   v) \<in> entry_range_asid_tags e}))
                                  \<union> all_non_fault_entries \<rparr>)} "

(* print_context *)                      
  instance ..
end



definition 
  incon_load :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> vaddr) set"
  where
  "incon_load snp a m rt \<equiv> (\<lambda>v. (a, v) ) ` 
                            {v. \<exists>x. snp a v = Hit x \<and> (x \<noteq> the (pt_walk a m rt v) \<and> \<not>is_fault (pt_walk a m rt v) \<or>
                                                       is_fault (pt_walk a m rt v) )}"

definition 
  miss_to_hit :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> vaddr) set"
 where
  "miss_to_hit snp a m rt \<equiv> (\<lambda>v. (a, v) ) ` 
                              {v. snp a v = Miss \<and>  \<not>is_fault (pt_walk a m rt v)}"

definition 
  consistent_hit :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> (asid \<times> vaddr) set"
 where
  "consistent_hit snp a m rt \<equiv> (\<lambda>v. (a, v) ) ` 
                                 {v. snp a v = Hit (the (pt_walk a m rt v)) \<and> \<not>is_fault (pt_walk a m rt v)}"



definition 
  snapshot_update_new :: "(asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> 
                          heap \<Rightarrow> ttbr0 \<Rightarrow>  (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_new iset' m_to_h h_to_h hp ttbr0 \<equiv> (\<lambda>x y. if (x,y) \<in>  iset' then Incon 
                                                     else if (x,y) \<in> m_to_h then Hit (the (pt_walk x hp ttbr0 y)) 
                                                     else if (x,y) \<in> h_to_h then Hit (the(pt_walk x hp ttbr0 y)) 
                                                     else Miss)"

definition 
  snapshot_update_new' :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)  \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> 
                          heap \<Rightarrow> ttbr0 \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_new' snp iset' m_to_h h_to_h hp ttbr0 a \<equiv> 
                     snp (a := snapshot_update_new iset' m_to_h h_to_h hp ttbr0 a)"


definition 
  snapshot_update_current :: "(asid \<times> vaddr) set \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow>(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_current iset' mem ttbr0  \<equiv> (\<lambda>x y. if (x,y) \<in>  iset' then Incon else 
                            if (\<not>is_fault (pt_walk x mem ttbr0 y)) then  Hit (the (pt_walk x mem ttbr0 y)) else Miss)"



definition 
  snapshot_update_current' :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> (asid \<times> vaddr) set \<Rightarrow> 
                      heap \<Rightarrow> ttbr0 \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_current' snp iset' mem ttbr0 a \<equiv> snp (a := snapshot_update_current iset' mem ttbr0 a)"



 

definition 
  incon_load2 :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr set"
  where
  "incon_load2 snp a m rt \<equiv>   {v. \<exists>x. snp a v = Hit x \<and> (x \<noteq> the (pt_walk a m rt v) \<and> \<not>is_fault (pt_walk a m rt v) \<or>
                                                       is_fault (pt_walk a m rt v) )}"


definition 
  incon_load_incon:: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> asid \<Rightarrow> heap \<Rightarrow> ttbr0 \<Rightarrow> vaddr set"
  where
  "incon_load_incon snp a m rt \<equiv>  {v. snp a v = Incon}"


definition 
  snapshot_update_current2 :: "vaddr set \<Rightarrow> heap \<Rightarrow> ttbr0  \<Rightarrow> (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_current2 iset' mem ttbr0  \<equiv> (\<lambda>a v. if v \<in>  iset' then Incon else 
                            if (\<not>is_fault (pt_walk a mem ttbr0 v)) then  Hit (the(pt_walk a mem ttbr0 v)) else Miss)"


definition 
  snapshot_update_current'2 :: "(asid \<Rightarrow> vaddr \<Rightarrow> lookup_type) \<Rightarrow> vaddr set \<Rightarrow> 
                                 heap \<Rightarrow> ttbr0 \<Rightarrow> asid \<Rightarrow> (asid \<Rightarrow> vaddr \<Rightarrow> lookup_type)"
where
  "snapshot_update_current'2 snp iset' mem ttbr0 a \<equiv> snp (a := snapshot_update_current2 iset' mem ttbr0 a)"


instantiation tlb_incon_state'_ext :: (type) reg_tlb_op   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      ttbr0   <- read_state TTBR0;
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      iset   <- read_state tlb_incon_set';
      asid   <- read_state ASID;
      mem    <- read_state MEM;
       let ptable_asid_va = ptable_comp asid mem mem ttbr0 r; 
       let incon_set_n = incon_set iset \<union> ptable_asid_va;
       let iset = iset \<lparr>incon_set := incon_set_n \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset \<rparr>)
} "


definition
  "(update_ASID a :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      tlb_incon_set   <- read_state tlb_incon_set';
      let iset = incon_set tlb_incon_set;  
      let snapshot = tlb_snapshot tlb_incon_set;
      let iset_current = ({asid} \<times> UNIV) \<inter> iset; 
      let snapshot_current = snapshot_update_current' snapshot iset_current mem ttbr0 asid;
      let tlb_incon_set = tlb_incon_set \<lparr>tlb_snapshot := snapshot_current \<rparr>;
      update_state (\<lambda>s. s\<lparr>tlb_incon_set' := tlb_incon_set \<rparr>);

      (* new ASID *)
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>);
      
     let iset_snp = incon_load snapshot_current a mem ttbr0; 
     let tlb_incon_set = tlb_incon_set\<lparr> incon_set:= iset \<union> iset_snp  \<rparr>;
     update_state (\<lambda>s. s\<lparr> tlb_incon_set' := tlb_incon_set \<rparr>)
} "

 definition   
  "(Flush_TLB  :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := {} , tlb_snapshot := \<lambda> a v . Miss \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset \<rparr>)
} "   

  definition   
  "(Flush_ASID  a :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := incon_set(iset) - {a} \<times> UNIV, 
                       tlb_snapshot := (tlb_snapshot iset)(a := \<lambda>v. Miss) \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset\<rparr>)
} "
    
definition   
  "(Flush_varange  vset :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := incon_set(iset) - UNIV \<times> vset , 
                 tlb_snapshot := \<lambda>x y. if (x, y) \<in> UNIV \<times> vset then Miss else tlb_snapshot iset x y \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset\<rparr>)
} "

definition   
  "(Flush_ASIDvarange  a vset :: ('a tlb_incon_state'_scheme \<Rightarrow> _))  = do {
      iset   <- read_state tlb_incon_set';
      let iset = iset \<lparr>incon_set := incon_set(iset) - {a} \<times> vset, 
                 tlb_snapshot := \<lambda>x y. if (x, y) \<in> {a} \<times> vset then Miss else tlb_snapshot iset x y \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set' := iset\<rparr>) } "
  instance ..
end






instantiation tlb_incon_state_ext :: (type) reg_tlb_op   
begin
  definition   
  "(update_TTBR0 r :: ('a tlb_incon_state_scheme \<Rightarrow> _))  = do {
      ttbr0   <- read_state TTBR0;
      update_state (\<lambda>s. s\<lparr> TTBR0 := r \<rparr>);
      iset_snapshot   <- read_state tlb_incon_set;
      asid   <- read_state ASID;
      mem    <- read_state MEM;
       let ptable_asid_va = ptable_comp' asid mem mem ttbr0 r; 
       let incon_set_n = iset iset_snapshot \<union>  ptable_asid_va;
       let iset_snapshot = iset_snapshot \<lparr>iset := incon_set_n \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := iset_snapshot \<rparr>)
} "


definition
  "(update_ASID a :: ('a tlb_incon_state_scheme \<Rightarrow> _))  = do {
      mem   <- read_state MEM;
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      tlb_incon_set   <- read_state tlb_incon_set;
      let iset = iset tlb_incon_set;  
      let snapshot = snapshot tlb_incon_set;
      let snapshot_current = snapshot_update_current'2 snapshot iset mem ttbr0 asid;
      let tlb_incon_set = tlb_incon_set \<lparr>snapshot := snapshot_current \<rparr>;
      update_state (\<lambda>s. s\<lparr>tlb_incon_set := tlb_incon_set \<rparr>);

      (* new ASID *)
      update_state (\<lambda>s. s\<lparr> ASID := a \<rparr>);

     let iset_snp_incon = incon_load_incon snapshot_current a mem ttbr0;
     let iset_snp = incon_load2 snapshot_current a mem ttbr0; 
     let tlb_incon_set = tlb_incon_set\<lparr> iset := iset_snp_incon \<union> iset_snp  \<rparr>;
     update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set \<rparr>)
} "



 definition   
  "(Flush_TLB  :: ('a tlb_incon_state_scheme \<Rightarrow> _))  = do {
      tlb_incon_set   <- read_state tlb_incon_set;
      let tlb_incon_set' = tlb_incon_set \<lparr>iset := {} , snapshot := \<lambda> a v . Miss \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set' \<rparr>)
} " 


  definition   
  "(Flush_ASID  a :: ('a tlb_incon_state_scheme \<Rightarrow> _))  = do {
      tlb_incon_set   <- read_state tlb_incon_set;
      asid   <- read_state ASID;
      if a = asid then 
      do { 
      let tlb_incon_set = tlb_incon_set \<lparr>iset := {} \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set\<rparr>)
           }
      else 
      do { 
      let tlb_incon_set = tlb_incon_set \<lparr> snapshot := (snapshot tlb_incon_set)(a := \<lambda>v. Miss) \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set\<rparr>)
      }
} "


    
definition   
  "(Flush_varange  vset :: ('a tlb_incon_state_scheme \<Rightarrow> _))  = do {
      tlb_incon_set   <- read_state tlb_incon_set;
      let tlb_incon_set = tlb_incon_set \<lparr>iset := iset(tlb_incon_set) - vset , 
                 snapshot := \<lambda>x y. if (x, y) \<in> UNIV \<times> vset then Miss else snapshot tlb_incon_set x y \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set\<rparr>)
} "

definition   
  "(Flush_ASIDvarange  a vset :: ('a tlb_incon_state_scheme \<Rightarrow> _))  = do {
      tlb_incon_set   <- read_state tlb_incon_set;
      asid  <- read_state ASID;
      if a = asid then 
      do { 
       let tlb_incon_set = tlb_incon_set \<lparr>iset := iset(tlb_incon_set) - vset \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set\<rparr>) 
           }
      else 
      do { 
       let tlb_incon_set = tlb_incon_set \<lparr>snapshot := \<lambda>x y. if (x, y) \<in> {a} \<times> vset then Miss else snapshot tlb_incon_set x y \<rparr>;
      update_state (\<lambda>s. s\<lparr> tlb_incon_set := tlb_incon_set\<rparr>) 
      }
} " 
  instance ..
end



end