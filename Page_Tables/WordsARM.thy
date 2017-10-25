(* @LICENSE(NICTA_CORE) *)

theory WordsARM
imports "HOL-Word.Word"
begin

class word_len_1 = len +
  assumes word_len_1: "len_of TYPE('a) = 1"

class word_len_1_2 = len +
  assumes word_len_1_2: "len_of TYPE('a) = 1 \<or> len_of TYPE('a) = 2"

class word_len_1_2_4 = len + 
  assumes word_len_1_2_4: "len_of TYPE('a) = 1 \<or> len_of TYPE('a) = 2 \<or> len_of TYPE('a) = 4"

class word_len_2_4_8 = len + 
  assumes word_len_2_4_8: "len_of TYPE('a) = 2 \<or> len_of TYPE('a) = 4 \<or> len_of TYPE('a) = 8"

class word_len_4_8_16 = len + 
  assumes word_len_4_8_16: "len_of TYPE('a) = 4 \<or> len_of TYPE('a) = 8 \<or> len_of TYPE('a) = 16"

class word_len_8_16_32 = len + 
  assumes word_len_8_16_32: "len_of TYPE('a) = 8 \<or> len_of TYPE('a) = 16 \<or> len_of TYPE('a) = 32"

instance num1 :: word_len_1
  by (intro_classes, simp)

instance num1 :: word_len_1_2
  by (intro_classes, simp)

instance num1 :: word_len_1_2_4
  by (intro_classes, simp)

instance bit0 :: (word_len_1) word_len_1_2
  by (intro_classes, simp add: word_len_1)

instance bit0 :: (word_len_1_2) word_len_1_2_4
  by (intro_classes, insert word_len_1_2, simp)

instance bit0 :: (word_len_1_2_4) word_len_2_4_8
  by (intro_classes, insert word_len_1_2_4, simp)

instance bit0 :: (word_len_2_4_8) word_len_4_8_16
  by (intro_classes, insert word_len_2_4_8, simp)

instance bit0 :: (word_len_4_8_16) word_len_8_16_32
  by (intro_classes, insert word_len_4_8_16, simp)

end
