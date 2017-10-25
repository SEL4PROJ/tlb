(* @LICENSE(NICTA_CORE) *)

(*  Author:     Rafal Kolanski, NICTA & UNSW 

    Instantiation of words (the isabelle type) whose size in bits is a 
    multiple of 8 to the mem_type class.
*)

theory WordTypes
imports MemTypes WordsARM
begin

lemma arm_same_addr_spaces [simp]:
  "addr_space_size = memory_size"
  by (simp add: addr_space_size memory_size)

instantiation "word" :: (word_len_8_16_32) mem_type
begin

definition
  "to_bytes_word \<equiv> machine_w2b"
definition
  "from_bytes_word \<equiv> machine_b2w"
definition
  size_of_word :: "'a word itself \<Rightarrow> nat" where
  "size_of_word x \<equiv> size (undefined::'a word) div 8"
definition
  align_of_word :: "'a word itself \<Rightarrow> nat" where
  "align_of_word \<equiv> size_of"
definition
  type_tag_word :: "'a word itself \<Rightarrow> type_tag" where
  "type_tag_word x \<equiv> ''word'' @ replicate (size_of x) (CHR ''1'')"
  (*XXX: picked up the sizing hack from Harvey, don't feel like playing with strings*)

lemma len_dvd: "\<lbrakk> len_of TYPE('a) = y ; x dvd y \<rbrakk> \<Longrightarrow> x dvd len_of TYPE('a)"
  by (erule dvdE, simp)

lemma dvd8: "8 dvd len_of TYPE('a)"
  by (insert word_len_8_16_32, auto intro: len_dvd)

lemma div8_same: "(7 + len_of TYPE('a)) div 8 = len_of TYPE('a) div 8"
proof - 
  from dvd8 show ?thesis by - (erule dvdE, simp)
qed

lemma some_bytes: "0 < len_of TYPE('a) div 8"
proof -
  have "0 < len_of TYPE('a)" by simp
  with dvd8 show ?thesis by - (erule dvdE, simp)
qed

lemma max_length:
  "len_of TYPE('a) div 8 < memory_size"
  using word_len_8_16_32 [where 'a='a]
  by (auto simp: memory_size)

lemma size_dvd_memory:
  "len_of TYPE('a) div 8 dvd memory_size"
  using word_len_8_16_32 [where 'a='a]
  by (auto simp: memory_size)

lemma w2b_b2w_id: 
  "\<lbrakk> length bs = (len_of TYPE('a)) div 8 \<rbrakk> 
   \<Longrightarrow>  machine_w2b ((machine_b2w bs)::'a word) = bs"
  using word_len_8_16_32 [where 'a='a]
  by (auto simp: machine_b2w_def machine_w2b_def 
                 word_rsplit_rcat_size word_size)

lemma restorable_word: 
  "length bs = size_of TYPE('a word) 
   \<Longrightarrow> to_bytes ((from_bytes bs)::('a word)) = bs"
  using word_len_8_16_32 [where 'a='a]
  by (auto simp: to_bytes_word_def from_bytes_word_def w2b_b2w_id 
                 size_of_word_def word_size)

instance
  using restorable_word
  by (intro_classes)
     (auto simp: to_bytes_word_def from_bytes_word_def size_of_word_def 
                    align_of_word_def
                    machine_b2w_def machine_w2b_def
                    word_rcat_rsplit length_word_rsplit_exp_size' word_size
                    div8_same some_bytes max_length size_dvd_memory)
end

text \<open>Size simplifications\<close>

lemma size_of_8 [simp]: "size_of TYPE(8 word) = 1"
  by (auto simp: size_of_word_def word_size)

lemma size_of_16 [simp]: "size_of TYPE(16 word) = 2"
  by (auto simp: size_of_word_def word_size)

lemma size_of_32 [simp]: "size_of TYPE(32 word) = 4"
  by (auto simp: size_of_word_def word_size)

declare align_of_word_def [simp]

text \<open>Simple tests checking little-endianess\<close>

lemma "to_bytes (0xAA :: byte) = [0xAA]"
  by (simp add: to_bytes_word_def machine_w2b_def)

lemma "to_bytes (0xEEAA :: 16 word) = [0xAA,0xEE]"
  by (simp add: to_bytes_word_def machine_w2b_def)

lemma "to_bytes (0xFFDDEEAA :: 32 word) = [0xAA,0xEE,0xDD,0xFF]"
  by (simp add: to_bytes_word_def machine_w2b_def)

end
