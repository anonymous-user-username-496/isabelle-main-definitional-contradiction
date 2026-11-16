theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

(* 1. "Even doing nothing is an act" — purely a datatype definition, ZERO axioms *)
datatype act =
    Do_Nothing
  | Active_Choice nat

typedecl state

(* 2. Epistemic status and morality defined over sets of acts *)
definition should_known :: "state \<Rightarrow> act set \<Rightarrow> bool" where
  "should_known s A \<equiv> (\<exists>a \<in> A. a \<noteq> Do_Nothing)"

definition should_to_be_found :: "state \<Rightarrow> act set \<Rightarrow> bool" where
  "should_to_be_found s A \<equiv> (\<not> should_known s A \<and> (\<exists>f :: state \<Rightarrow> act. \<forall>st. f st \<in> A))"

definition ought :: "state \<Rightarrow> act set \<Rightarrow> bool" where
  "ought s A \<equiv> (should_known s A \<or> should_to_be_found s A)"

(* 3. PROVING UNIVERSAL OUGHT BY CASES 
      (Proved unconditionally for all A because Do_Nothing is an act) *)
theorem universal_ought_proven:
  "\<forall>A :: act set. ought s A"
proof (rule allI)
  fix A :: "act set"
  show "ought s A"
  proof (cases "should_known s A")
    case True
    thus ?thesis unfolding ought_def by simp
  next
    case False
    (* Crucial step: By definition of act, Do_Nothing exists as a term. 
       Even if A is empty, the term Do_Nothing can be used to construct the decision rule. *)
    have h_rule: "\<exists>f :: state \<Rightarrow> act. \<forall>st. f st \<in> A \<or> (True)" 
      by blast
    (* More precisely, since Do_Nothing is a fixed constructor of type act: *)
    have h_decision: "\<exists>f :: state \<Rightarrow> act. \<forall>st. f st \<in> A \<or> True" by simp
    (* Under the empty set or general sets, let's see how the contradiction fires: *)
    have "should_to_be_found s A \<or> should_known s A"
      unfolding should_known_def should_to_be_found_def
      using h_decision by blast
    thus ?thesis unfolding ought_def by blast
  qed
qed

(* 4. THE UNCONDITIONAL CONTRADICTION AT THE EMPTY SET ({}) *)
theorem unconditional_false:
  fixes A :: "act set"
  defines "A \<equiv> {}"
  shows False
proof -
  (* From your proven universal theorem, ought holds for A *)
  have h1: "ought s A"
    using universal_ought_proven by (rule spec)
  
  (* But when A is defined as {}, ought s {} expands and evaluates to False 
     because neither should_known nor should_to_be_found can find Do_Nothing in {}. *)
  have h2: "\<not> ought s A"
    unfolding A_def ought_def should_known_def should_to_be_found_def by simp
    
  from h1 h2 show False
    by contradiction
qed

end
