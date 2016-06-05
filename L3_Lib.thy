(*  Title: L3_Lib.thy
    Author: Anthony Fox, University of Cambridge

L3 operations.
*)

theory L3_Lib
imports "$ISABELLE_HOME/src/HOL/Word/Word"
        "$ISABELLE_HOME/src/HOL/Library/Code_Target_Numeral"
        "$ISABELLE_HOME/src/HOL/Library/Code_Char"
        "~~/src/HOL/Library/Monad_Syntax"
begin

(* enable printing for do notation *)
translations
  "_do_block (_do_cons (_do_bind p t) (_do_final e))"
    <= "CONST bind t (\<lambda>p. e)"

(* avoid syntax clash with shift-right operation *)
no_syntax
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)


(* basic state Monad *)

definition "return = Pair"
declare return_def [simp add]

fun bind :: "('state \<Rightarrow> ('a \<times> 'state)) \<Rightarrow>
             ('a \<Rightarrow> 'state \<Rightarrow> ('b \<times> 'state)) \<Rightarrow>
             ('state \<Rightarrow> ('b \<times> 'state))" where
  "bind f g = (\<lambda>s. let (a, s') = f s in g a s')"

(* use do syntax for this state monad *)
adhoc_overloading
  Monad_Syntax.bind bind

fun read_state :: "('state \<Rightarrow> 'a) \<Rightarrow> 'state \<Rightarrow> 'a \<times> 'state" where
  "read_state f = (\<lambda>s. (f s, s))"

fun update_state :: "('state \<Rightarrow> 'state) \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state" where
  "update_state f = (\<lambda>s. ((), f s))"

fun extend_state :: "'b \<Rightarrow> ('b \<times> 'state \<Rightarrow> 'a \<times> 'b \<times> 'state) \<Rightarrow> 'state \<Rightarrow> 'a \<times> 'state" where
  "extend_state v f = (\<lambda>s. let (a, s') = f (v, s) in (a, snd s'))"

fun trim_state :: "('state \<Rightarrow> 'a \<times> 'state) \<Rightarrow> 'b \<times> 'state \<Rightarrow> 'a \<times> 'b \<times> 'state" where
  "trim_state f = (\<lambda>(s1, s2). let (a, s') = f s2 in (a, s1, s'))"

fun foreach_loop :: "'a list \<times> ('a \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state) \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state" where
  "foreach_loop ([], _) = return ()" |
  "foreach_loop (h # t, a) = bind (a h) (\<lambda>u. foreach_loop (t, a))"

function for_loop :: "nat \<times> nat \<times> (nat \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state) \<Rightarrow> 'state \<Rightarrow> unit \<times> 'state" where
  "for_loop (i, j, a) =
   (if i = j then
      a i
    else
      bind (a i) (\<lambda>u. for_loop ((if i < j then i + 1 else i - 1), j, a)))"
  by auto
  termination by (relation "measure (\<lambda>(i, j, _). if i < j then j - i else i - j)") auto

(* extra character operations *)

fun Ord :: "char \<Rightarrow> nat" where
   "Ord (Char nh nl) = nat_of_nibble nh * 16 + nat_of_nibble nl"

fun Chr :: "nat \<Rightarrow> char" where
   "Chr n = Char (nibble_of_nat (n div 16)) (nibble_of_nat n)"

fun is_lower :: "char \<Rightarrow> bool" where
   "is_lower c = (Ord (CHR ''a'') \<le> Ord c \<and> Ord c \<le> Ord (CHR ''z''))"

fun is_upper :: "char \<Rightarrow> bool" where
   "is_upper c = (Ord (CHR ''A'') \<le> Ord c \<and> Ord c \<le> Ord (CHR ''Z''))"

fun is_space :: "char \<Rightarrow> bool" where
   "is_space c = (Ord (CHR '' '') = Ord c \<or> 9 \<le> Ord c \<and> Ord c \<le> 13)"

fun is_digit :: "char \<Rightarrow> bool" where
   "is_digit c = (Ord (CHR ''0'') \<le> Ord c \<and> Ord c \<le> Ord (CHR ''9''))"

fun is_hex_digit :: "char \<Rightarrow> bool" where
   "is_hex_digit c = (is_digit c \<or> Ord (CHR ''a'') \<le> Ord c \<and> Ord c \<le> Ord (CHR ''f'') \<or>
                                   Ord (CHR ''A'') \<le> Ord c \<and> Ord c \<le> Ord (CHR ''F''))"

fun is_alpha :: "char \<Rightarrow> bool" where
   "is_alpha c = (is_lower c \<or> is_upper c)"

fun is_alpha_num :: "char \<Rightarrow> bool" where
   "is_alpha_num c = (is_alpha c \<or> is_digit c)"

fun to_lower :: "char \<Rightarrow> char" where
   "to_lower c = (if is_upper c then Chr (Ord c + 32) else c)"

fun to_upper :: "char \<Rightarrow> char" where
   "to_upper c = (if is_lower c then Chr (Ord c - 32) else c)"

(* numeric strings *)

fun list_to_nat :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "list_to_nat _ [] = 0" |
  "list_to_nat base (h # t) = h mod base + base * list_to_nat base t"

fun nat_to_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "nat_to_list base n =
   (if n < base \<or> base < 2 then [n mod base] else n mod base # nat_to_list base (n div base))"

fun hex :: "nat \<Rightarrow> char" where
  "hex n = (if n = 0 then CHR ''0''
            else if n = 1 then CHR ''1''
            else if n = 2 then CHR ''2''
            else if n = 3 then CHR ''3''
            else if n = 4 then CHR ''4''
            else if n = 5 then CHR ''5''
            else if n = 6 then CHR ''6''
            else if n = 7 then CHR ''7''
            else if n = 8 then CHR ''8''
            else if n = 9 then CHR ''9''
            else if n = 10 then CHR ''A''
            else if n = 11 then CHR ''B''
            else if n = 12 then CHR ''C''
            else if n = 13 then CHR ''D''
            else if n = 14 then CHR ''E''
            else if n = 15 then CHR ''F''
            else undefined)"

fun unhex :: "char \<Rightarrow> nat" where
  "unhex c = (if c = CHR ''0'' then 0
              else if c = CHR ''1'' then 1
              else if c = CHR ''2'' then 2
              else if c = CHR ''3'' then 3
              else if c = CHR ''4'' then 4
              else if c = CHR ''5'' then 5
              else if c = CHR ''6'' then 6
              else if c = CHR ''7'' then 7
              else if c = CHR ''8'' then 8
              else if c = CHR ''9'' then 9
              else if c = CHR ''a'' \<or> c = CHR ''A'' then 10
              else if c = CHR ''b'' \<or> c = CHR ''B'' then 11
              else if c = CHR ''c'' \<or> c = CHR ''C'' then 12
              else if c = CHR ''d'' \<or> c = CHR ''D'' then 13
              else if c = CHR ''e'' \<or> c = CHR ''E'' then 14
              else if c = CHR ''f'' \<or> c = CHR ''F'' then 15
              else undefined)"

fun string_to_nat :: "nat \<Rightarrow> string \<Rightarrow> nat" where
  "string_to_nat base s = list_to_nat base (map unhex (rev s))"

fun nat_to_string :: "nat \<Rightarrow> nat \<Rightarrow> string" where
  "nat_to_string base n = rev (map hex (nat_to_list base n))"

definition "bin_string_to_nat \<equiv> string_to_nat 2"
definition "nat_to_bin_string \<equiv> nat_to_string 2"
definition "dec_string_to_nat \<equiv> string_to_nat 10"
definition "nat_to_dec_string \<equiv> nat_to_string 10"
definition "hex_string_to_nat \<equiv> string_to_nat 16"
definition "nat_to_hex_string \<equiv> nat_to_string 16"

fun nat_from_bin_string :: "string \<Rightarrow> nat option" where
  "nat_from_bin_string s =
   (if s \<noteq> '''' \<and> list_all (\<lambda>c. c = CHR ''0'' \<or> c = CHR ''1'') s then
      Some (bin_string_to_nat s)
    else None)"

fun nat_from_dec_string :: "string \<Rightarrow> nat option" where
  "nat_from_dec_string s =
   (if s \<noteq> '''' \<and> list_all is_digit s then Some (dec_string_to_nat s) else None)"

fun nat_from_hex_string :: "string \<Rightarrow> nat option" where
  "nat_from_hex_string s =
   (if s \<noteq> '''' \<and> list_all is_hex_digit s then Some (hex_string_to_nat s) else None)"

fun dec_string_to_int :: "string \<Rightarrow> int" where
  "dec_string_to_int (CHR ''-'' # r) = -int (dec_string_to_nat r)" |
  "dec_string_to_int (CHR ''~'' # r) = -int (dec_string_to_nat r)" |
  "dec_string_to_int r = int (dec_string_to_nat r)"

fun int_to_dec_string :: "int \<Rightarrow> string" where
  "int_to_dec_string i =
   (if i < 0 then CHR ''~'' # nat_to_dec_string (nat (-i)) else nat_to_dec_string (nat i))"

fun string_to_bool :: "string \<Rightarrow> bool" where
  "string_to_bool s = (if s = ''true'' then True
                       else if s = ''false'' then False
                       else undefined)"

fun string_to_char :: "string \<Rightarrow> char" where
  "string_to_char [c] = c" |
  "string_to_char _ = undefined"

(* extra Nat operation *)

fun log2 :: "nat \<Rightarrow> nat" where
  "log2 n = (if n = 0 then undefined else if n = 1 then 0 else Suc (log2 (n div 2)))"

(* extra int operations *)

fun quot :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "quot" 70) where
  "i quot j = (if j = 0 then undefined
               else if 0 < j then if 0 \<le> i then i div j else -(-i div j)
               else if 0 \<le> i then -(i div -j)
               else -i div -j)"

fun rem :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "rem" 70) where
  "i rem j = (if j = 0 then undefined else i - i quot j * j)"

fun quot_rem :: "int * int \<Rightarrow> int * int" where
  "quot_rem (i, j) = (i div j, i rem j)"

(* extra option operations *)

fun is_some :: "'a option \<Rightarrow> bool" where
  "is_some (Some _) = True" |
  "is_some _ = False"

(* extra list operations *)

fun splitl :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "splitl _ [] = ([], [])" |
  "splitl P (h # t) = (if P h then let (l, r) = splitl P t in (h # l, r) else ([], h # t))"

fun splitr :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "splitr P x = (let (l, r) = splitl P (rev x) in (rev r, rev l))"

fun pad_left :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pad_left c n s = replicate (n - length s) c @ s"

fun pad_right :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pad_right c n s = s @ replicate (n - length s) c"

fun index_find :: "nat \<Rightarrow> 'a \<times> 'a list \<Rightarrow> nat option" where
  "index_find _ (_, []) = None" |
  "index_find i (v, h # t) = (if v = h then Some i else index_find (Suc i) (v, t))"

definition "index_of = index_find 0"
declare index_of_def [simp add]

fun remove :: "'a list * 'a list \<Rightarrow> 'a list" where
  "remove (l1, l2) = filter (\<lambda>x. x \<notin> set l1) l2"

fun remove_except :: "'a list * 'a list \<Rightarrow> 'a list" where
  "remove_except (l1, l2) = filter (\<lambda>x. x \<in> set l1) l2"

fun remove_duplicates :: "'a list \<Rightarrow> 'a list" where
  "remove_duplicates [] = []" |
  "remove_duplicates (h # t) = (if h \<in> set t then remove_duplicates t else h # remove_duplicates t)"

(* extra string operations *)

lemma splitl_length [simp]:
  shows "length (snd (splitl P x)) \<le> length x"
  by (induct x, auto simp add: case_prod_beta)

lemma fields_termination_lem [simp]:
  assumes "a \<noteq> []" and "length a \<le> length c"
  shows "length a - b < Suc (length c)"
  by (simp add: assms(2) le_imp_less_Suc less_imp_diff_less)

function (sequential) tokens :: "(char \<Rightarrow> bool) \<Rightarrow> string \<Rightarrow> string list" where
  "tokens _ '''' = []" |
  "tokens P x =
   (let (l, r) = splitl (\<lambda>e. ~P e) x in if l = [] then tokens P (tl r) else l # tokens P r)"
  by pat_completeness auto
  termination tokens
  apply (relation "measure (length o snd)")
  apply auto
  apply (case_tac "~ P v", auto simp add: case_prod_beta le_imp_less_Suc)
  apply (case_tac "~ P v", auto simp add: case_prod_beta le_imp_less_Suc)
  done

function (sequential) fields :: "(char \<Rightarrow> bool) \<Rightarrow> string \<Rightarrow> string list" where
  "fields _ '''' = [[]]" |
  "fields P x =
   (let (l, r) = splitl (\<lambda>e. ~P e) x in if l = [] then [] # fields P (tl r)
                                        else if r = [] then [l]
                                        else l # fields P (tl r))"
  by pat_completeness auto
  termination fields
  apply (relation "measure (length o snd)")
  apply auto
  apply (case_tac "~ P v", auto simp add: case_prod_beta le_imp_less_Suc)
  apply (case_tac "~ P v", auto simp add: case_prod_beta)
  done

(* bit-string operations - extends Bool_List_Representation.thy *)

fun nat_to_bitstring :: "nat \<Rightarrow> bool list" where
  "nat_to_bitstring 0 = [False]" |
  "nat_to_bitstring n = bin_to_bl (log2 n + 1) (int n)"

definition "bitstring_to_nat = nat o bl_to_bin"

fun fixwidth :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "fixwidth n v = (let l = length v in if l < n then pad_left False n v else drop (l - n) v)"

fun bitwise :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "bitwise f v1 v2 =
   (let m = max (length v1) (length v2) in map (case_prod f) (zip (fixwidth m v1) (fixwidth m v2)))"

definition "bor  = bitwise (op \<or>)"
definition "band = bitwise (op \<and>)"
definition "bxor = bitwise (op \<noteq>)"

fun bitstring_shiftl :: "bool list \<Rightarrow> nat \<Rightarrow> bool list" where
  "bitstring_shiftl v m = pad_right False (length v + m) v"

fun bitstring_shiftr :: "bool list \<Rightarrow> nat \<Rightarrow> bool list" where
  "bitstring_shiftr v m = take (length v - m) v"

fun bitstring_field :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "bitstring_field h l v = fixwidth (Suc h - l) (bitstring_shiftr v l)"

fun bitstring_rotate :: "bool list \<Rightarrow> nat \<Rightarrow> bool list" where
  "bitstring_rotate v m =
   (let l = length v in
    let x = m mod l in
      if l = 0 \<or> x = 0 then v else bitstring_field (x - 1) 0 v @ bitstring_field (l - 1) x v)"

fun bitstring_test_bit :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
  "bitstring_test_bit v n = (bitstring_field n n v = [True])"

fun bitstring_modify ::  "(nat \<times> bool \<Rightarrow> bool) \<times> bool list \<Rightarrow> bool list" where
  "bitstring_modify (f, l) = map f (zip (rev (upt 0 (length l))) l)"

fun bitstring_field_insert :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "bitstring_field_insert h l v1 v2 =
   bitstring_modify (\<lambda>(i, b). if l \<le> i \<and> i \<le> h then bitstring_test_bit v1 (i - l) else b, v2)"

(* extra word operations *)

fun unsigned_min :: "'a::len word \<times> 'a::len word \<Rightarrow> 'a::len word" where
  "unsigned_min (w1, w2) = (if w1 \<le> w2 then w1 else w2)"

fun unsigned_max :: "'a::len word \<times> 'a::len word \<Rightarrow> 'a::len word" where
  "unsigned_max (w1, w2) = (if w1 \<le> w2 then w2 else w1)"

fun word_log2 :: "'a::len word \<Rightarrow> 'a::len word" where
  "word_log2 w = of_nat (log2 (unat w))"

fun word_quot :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
  "word_quot i j = of_int (sint i quot sint j)"

fun word_rem :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
  "word_rem i j = of_int (sint i rem sint j)"

fun word_modify :: "(nat \<times> bool \<Rightarrow> bool) \<times> 'a::len word \<Rightarrow> 'a::len word" where
  "word_modify (f, w) = of_bl (bitstring_modify (f, to_bl w))"

fun word_bit_field_insert :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word" where
  "word_bit_field_insert h l w1 w2 =
   word_modify (\<lambda>(i, b). if l \<le> i \<and> i \<le> h then test_bit w1 (i - l) else b, w2)"

fun word_bits :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
  "word_bits h l w = (w >> l) AND mask (Suc h - l)"

fun word_extract :: "nat \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  "word_extract h l w = ucast (word_bits h l w)"

fun word_replicate :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  "word_replicate n a = word_rcat (replicate n a)"

(* floating-point stubs *)

datatype ieee_rounding =
  roundTiesToEven | roundTowardPositive | roundTowardNegative | roundTowardZero

datatype ieee_compare = LT | EQ | GT | UN

consts
  fp32_abs :: "32 word \<Rightarrow> 32 word"
  fp32_abs1985 :: "32 word \<Rightarrow> 32 word"
  fp32_add :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_compare :: "32 word \<Rightarrow> 32 word \<Rightarrow> ieee_compare"
  fp32_div :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_equal :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool"
  fp32_from_int :: "ieee_rounding \<Rightarrow> int \<Rightarrow> 32 word"
  fp32_greater :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool"
  fp32_greater_equal :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool"
  fp32_is_finite :: "32 word \<Rightarrow> bool"
  fp32_is_nan :: "32 word \<Rightarrow> bool"
  fp32_is_normal :: "32 word \<Rightarrow> bool"
  fp32_is_subnormal :: "32 word \<Rightarrow> bool"
  fp32_less :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool"
  fp32_less_equal :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool"
  fp32_mul :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_mul_add :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_mul_sub :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_neg_inf :: "32 word"
  fp32_neg_zero :: "32 word"
  fp32_negate :: "32 word \<Rightarrow> 32 word"
  fp32_negate1985 :: "32 word \<Rightarrow> 32 word"
  fp32_pos_inf :: "32 word"
  fp32_pos_zero :: "32 word"
  fp32_sqrt :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_sub :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
  fp32_to_int :: "ieee_rounding \<Rightarrow> 32 word \<Rightarrow> int option"

consts
  fp64_abs :: "64 word \<Rightarrow> 64 word"
  fp64_abs1985 :: "64 word \<Rightarrow> 64 word"
  fp64_add :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_compare :: "64 word \<Rightarrow> 64 word \<Rightarrow> ieee_compare"
  fp64_div :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_equal :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool"
  fp64_from_int :: "ieee_rounding \<Rightarrow> int \<Rightarrow> 64 word"
  fp64_greater :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool"
  fp64_greater_equal :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool"
  fp64_is_finite :: "64 word \<Rightarrow> bool"
  fp64_is_nan :: "64 word \<Rightarrow> bool"
  fp64_is_normal :: "64 word \<Rightarrow> bool"
  fp64_is_subnormal :: "64 word \<Rightarrow> bool"
  fp64_less :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool"
  fp64_less_equal :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool"
  fp64_mul :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_mul_add :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_mul_sub :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_neg_inf :: "64 word"
  fp64_neg_zero :: "64 word"
  fp64_negate :: "64 word \<Rightarrow> 64 word"
  fp64_negate1985 :: "64 word \<Rightarrow> 64 word"
  fp64_pos_inf :: "64 word"
  fp64_pos_zero :: "64 word"
  fp64_sqrt :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_sub :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
  fp64_to_int :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> int option"

consts
  fp32_to_fp64 :: "32 word \<Rightarrow> 64 word"
  fp64_to_fp32 :: "ieee_rounding \<Rightarrow> 64 word \<Rightarrow> 32 word"

code_printing
    constant "fp32_abs" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_abs\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_abs\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_abs\")"
  | constant "fp32_abs1985" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_abs1985\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_abs1985\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_abs1985\")"
  | constant "fp32_add" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp32'_add\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp32'_add\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp32'_add\")"
  | constant "fp32_compare" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_compare\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_compare\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_compare\")"
  | constant "fp32_div" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp32'_div\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp32'_div\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp32'_div\")"
  | constant "fp32_equal" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_equal\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_equal\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_equal\")"
  | constant "fp32_from_int" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_from'_int\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_from'_int\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_from'_int\")"
  | constant "fp32_greater" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_greater\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_greater\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_greater\")"
  | constant "fp32_greater_equal" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_greater'_equal\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_greater'_equal\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_greater'_equal\")"
  | constant "fp32_is_finite" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_is'_finite\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_is'_finite\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_is'_finite\")"
  | constant "fp32_is_nan" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_is'_nan\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_is'_nan\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_is'_nan\")"
  | constant "fp32_is_normal" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_is'_normal\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_is'_normal\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_is'_normal\")"
  | constant "fp32_is_subnormal" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_is'_subnormal\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_is'_subnormal\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_is'_subnormal\")"
  | constant "fp32_less" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_less\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_less\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_less\")"
  | constant "fp32_less_equal" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_less'_equal\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_less'_equal\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_less'_equal\")"
  | constant "fp32_mul" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp32'_mul\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp32'_mul\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp32'_mul\")"
  | constant "fp32_mul_add" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => fn '_ => raise Fail \"fp32'_mul'_add\")"
      and (OCaml) "!(fun '_ '_ '_ '_ -> failwith \"fp32'_mul'_add\")"
      and (Haskell) "!(\\ '_ '_ '_ '_ -> error \"fp32'_mul'_add\")"
  | constant "fp32_mul_sub" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => fn '_ => raise Fail \"fp32'_mul'_sub\")"
      and (OCaml) "!(fun '_ '_ '_ '_ -> failwith \"fp32'_mul'_sub\")"
      and (Haskell) "!(\\ '_ '_ '_ '_ -> error \"fp32'_mul'_sub\")"
  | constant "fp32_neg_inf" \<rightharpoonup>
      (SML) "!(raise Fail \"fp32'_neg'_inf\")"
      and (OCaml) "!(failwith \"fp32'_neg'_inf\")"
      and (Haskell) "!(error \"fp32'_neg'_inf\")"
  | constant "fp32_neg_zero" \<rightharpoonup>
      (SML) "!(raise Fail \"fp32'_neg'_zero\")"
      and (OCaml) "!(failwith \"fp32'_neg'_zero\")"
      and (Haskell) "!(error \"fp32'_neg'_zero\")"
  | constant "fp32_negate" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_negate\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_negate\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_negate\")"
  | constant "fp32_negate1985" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_negate1985\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_negate1985\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_negate1985\")"
  | constant "fp32_pos_inf" \<rightharpoonup>
      (SML) "!(raise Fail \"fp32'_pos'_inf\")"
      and (OCaml) "!(failwith \"fp32'_pos'_inf\")"
      and (Haskell) "!(error \"fp32'_pos'_inf\")"
  | constant "fp32_pos_zero" \<rightharpoonup>
      (SML) "!(raise Fail \"fp32'_pos'_zero\")"
      and (OCaml) "!(failwith \"fp32'_pos'_zero\")"
      and (Haskell) "!(error \"fp32'_pos'_zero\")"
  | constant "fp32_sqrt" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_sqrt\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_sqrt\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_sqrt\")"
  | constant "fp32_sub" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp32'_sub\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp32'_sub\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp32'_sub\")"
  | constant "fp32_to_int" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp32'_to'_int\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp32'_to'_int\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp32'_to'_int\")"
  | constant "fp64_abs" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_abs\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_abs\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_abs\")"
  | constant "fp64_abs1985" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_abs1985\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_abs1985\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_abs1985\")"
  | constant "fp64_add" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp64'_add\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp64'_add\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp64'_add\")"
  | constant "fp64_compare" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_compare\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_compare\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_compare\")"
  | constant "fp64_div" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp64'_div\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp64'_div\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp64'_div\")"
  | constant "fp64_equal" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_equal\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_equal\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_equal\")"
  | constant "fp64_from_int" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_from'_int\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_from'_int\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_from'_int\")"
  | constant "fp64_greater" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_greater\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_greater\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_greater\")"
  | constant "fp64_greater_equal" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_greater'_equal\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_greater'_equal\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_greater'_equal\")"
  | constant "fp64_is_finite" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_is'_finite\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_is'_finite\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_is'_finite\")"
  | constant "fp64_is_nan" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_is'_nan\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_is'_nan\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_is'_nan\")"
  | constant "fp64_is_normal" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_is'_normal\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_is'_normal\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_is'_normal\")"
  | constant "fp64_is_subnormal" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_is'_subnormal\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_is'_subnormal\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_is'_subnormal\")"
  | constant "fp64_less" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_less\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_less\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_less\")"
  | constant "fp64_less_equal" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_less'_equal\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_less'_equal\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_less'_equal\")"
  | constant "fp64_mul" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp64'_mul\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp64'_mul\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp64'_mul\")"
  | constant "fp64_mul_add" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => fn '_ => raise Fail \"fp64'_mul'_add\")"
      and (OCaml) "!(fun '_ '_ '_ '_ -> failwith \"fp64'_mul'_add\")"
      and (Haskell) "!(\\ '_ '_ '_ '_ -> error \"fp64'_mul'_add\")"
  | constant "fp64_mul_sub" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => fn '_ => raise Fail \"fp64'_mul'_sub\")"
      and (OCaml) "!(fun '_ '_ '_ '_ -> failwith \"fp64'_mul'_sub\")"
      and (Haskell) "!(\\ '_ '_ '_ '_ -> error \"fp64'_mul'_sub\")"
  | constant "fp64_neg_inf" \<rightharpoonup>
      (SML) "!(raise Fail \"fp64'_neg'_inf\")"
      and (OCaml) "!(failwith \"fp64'_neg'_inf\")"
      and (Haskell) "!(error \"fp64'_neg'_inf\")"
  | constant "fp64_neg_zero" \<rightharpoonup>
      (SML) "!(raise Fail \"fp64'_neg'_zero\")"
      and (OCaml) "!(failwith \"fp64'_neg'_zero\")"
      and (Haskell) "!(error \"fp64'_neg'_zero\")"
  | constant "fp64_negate" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_negate\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_negate\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_negate\")"
  | constant "fp64_negate1985" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp64'_negate1985\")"
      and (OCaml) "!(fun '_ -> failwith \"fp64'_negate1985\")"
      and (Haskell) "!(\\ '_ -> error \"fp64'_negate1985\")"
  | constant "fp64_pos_inf" \<rightharpoonup>
      (SML) "!(raise Fail \"fp64'_pos'_inf\")"
      and (OCaml) "!(failwith \"fp64'_pos'_inf\")"
      and (Haskell) "!(error \"fp64'_pos'_inf\")"
  | constant "fp64_pos_zero" \<rightharpoonup>
      (SML) "!(raise Fail \"fp64'_pos'_zero\")"
      and (OCaml) "!(failwith \"fp64'_pos'_zero\")"
      and (Haskell) "!(error \"fp64'_pos'_zero\")"
  | constant "fp64_sqrt" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_sqrt\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_sqrt\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_sqrt\")"
  | constant "fp64_sub" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => fn '_ => raise Fail \"fp64'_sub\")"
      and (OCaml) "!(fun '_ '_ '_ -> failwith \"fp64'_sub\")"
      and (Haskell) "!(\\ '_ '_ '_ -> error \"fp64'_sub\")"
  | constant "fp64_to_int" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_to'_int\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_to'_int\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_to'_int\")"
  | constant "fp32_to_fp64" \<rightharpoonup>
      (SML) "!(fn '_ => raise Fail \"fp32'_to'_fp64\")"
      and (OCaml) "!(fun '_ -> failwith \"fp32'_to'_fp64\")"
      and (Haskell) "!(\\ '_ -> error \"fp32'_to'_fp64\")"
  | constant "fp64_to_fp32" \<rightharpoonup>
      (SML) "!(fn '_ => fn '_ => raise Fail \"fp64'_to'_fp32\")"
      and (OCaml) "!(fun '_ '_ -> failwith \"fp64'_to'_fp32\")"
      and (Haskell) "!(\\ '_ '_ -> error \"fp64'_to'_fp32\")"

end
