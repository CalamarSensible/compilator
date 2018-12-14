(*Ceci est la première partie du compilateur de Simon Mirwasser*)
open Cparse
open Genlab

exception NotInList

let find_var x d vll = (* Cette fonction permet de trouver l'adresse d'une variable x à la profondeur inférieure ou égale à d la plus grande possible, et la considère comme variable globale si elle n'en trouve pas*)
  let rec find_with_dpt x d vll = match vll with
    |[] -> raise NotInList
    |(s,n,dpt)::q when (s,dpt) = (x,d) -> ((string_of_int ((-8)*n)) ^ "(%rbp)")
    |(s,n,dpt)::q -> find_with_dpt x d q in
  let rec browse x d vll = match d with
    |0 -> (x ^ "(%rip)")
    |_ -> try find_with_dpt x d vll with
      |NotInList -> browse x (d-1) vll
in browse x d vll

let rec suppr_dpt_list d l = match l with (*Supprime les variables ayant une profondeur supérieure ou égale à d, utilisée dans if et while*)
  |[] -> []
  |(s,n,dpt)::q when dpt >= n -> suppr_dpt_list d q
  |(s,n,dpt)::q -> (s,n,dpt)::(suppr_dpt_list d q)

let rec is_in_dpt x d l = match l with (*Evite que deux fois la meme variable soit déclarée à la meme profondeur*)
  |[] -> false
  |(s,n,dpt)::q when (s,dpt) = (x,d) -> true
  |(s,n,dpt)::q -> is_in_dpt x d q

let rec is_in x l = match l with (*Dit si un élément est dans une liste ou non, utile pour ne pas déclarer deux fois une variable globale*)
  |[] -> false
  |s::q when s = x -> true
  |s::q -> is_in x q

let reverse l = (*Reverse une liste*)
  let rec aux l l' = match l with
    |[] -> l'
    |t::q -> aux q (t::l')
in aux l []

let fst_list l = match l with (*Renvoie la tête d'une liste*)
  |[] -> raise NotInList
  |t::q -> t

let rec len l = match l with (*calcule la longueur d'une liste*)
  |[] -> 0
  |t::q -> 1+ (len q)

let max_2 a b = if a >= b then a else b

(* mes fonctions compile ont en argument fl qui est la liste des fonctions déjà compilées, vgl qui est la liste des variables globales de mon code, nlab qui est l'indice du prochai label, vll qui est la liste des variables locales d'une fonction avec leur profondeur et leur distance à rbp, n qui est la distance entre rbp et rsp que j'utilise pour connaître la distance entre une variable et rbp quand je la définit, dpt est la profondeur à laquelle je suis (cf readme), nlabs est l'indice de label de string et sl est la liste des string que je vois dans une fonction pour faire des labels vers ces string après chaque fonction*)

let compile out vdl =
  let write s = Printf.fprintf out "%s\n" s in
  write "\t .file \"test0.c\"";
  let rec compile_decl_list_ini vdl fl vgl nlab n nlabs = match vdl with
    |[] -> ()
    |vd::q -> let (fl2,vgl2,nlab2,n2,nlabs2) = compile_decl_ini vd fl vgl nlab n nlabs in compile_decl_list_ini q fl2 vgl2 nlab2 n2 nlabs2
  and compile_decl_ini vd fl vgl nlab n nlabs = match vd with
    |CDECL(l,s) -> if is_in s vgl then (fl,vgl,nlab,n,nlabs) else
        begin
        write ((".comm " ^ s) ^ ",8,8");
        (fl,s::vgl,nlab,n,nlabs)
        end
    |CFUN(l,s,vdl,(l1,c)) -> begin
       write "\t .text";
       write ("\t .globl " ^ s);
       write (("\t .type " ^ s) ^ ", @function");
       write (s ^ ":");
       write"\t pushq %rbp";
       write "\t movq %rsp, %rbp";
       let (vll,n2) = compile_decl_list_args vdl [] 1 0 in
       let (fl2,vgl2,nlab2,vll2,n3,dpt2,sl2,nlabs2) = (compile_code c (s::fl) vgl nlab vll n2 2 [] nlabs) in
       write ((".R" ^ (fst_list fl2)) ^ ":"); (* Permet de ne pas executer la suite du programme après un return*)
       write "\t leave";
       write "\t ret";
       write ((("\t .size " ^ s) ^ ", .-") ^ s);
       write "\t .section \t .rodata";
       compile_string sl2;
       (fl2,vgl2,(nlab2+1),n,nlabs2)
       end
  and compile_decl_list_args vdl al na n = match vdl with
    |[] -> (al,n)
    |CDECL(l,a)::q when na = 1 -> begin
        write "\t pushq %rdi";
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CDECL(l,a)::q when na = 2 -> begin
        write "\t pushq %rsi";
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CDECL(l,a)::q when na = 3 -> begin
        write "\t pushq %rdx";
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CDECL(l,a)::q when na = 4 -> begin
        write "\t pushq %rcx";
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CDECL(l,a)::q when na = 5 -> begin
        write "\t pushq %r8";
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CDECL(l,a)::q when na = 6 -> begin
        write "\t pushq %r9";
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CDECL(l,a)::q -> begin
        write (("\t pushq " ^ (string_of_int (8*(na-5)))) ^ "(%rbp)");
        compile_decl_list_args q ((a,n+1,1)::al) (na+1) (n+1)
          end
    |CFUN(l,s,nvdl,lc)::q -> failwith "No Function Here"
  and compile_var_decl_list vdl vll n dpt = match vdl with
    |[] -> (vll,n)
    |CDECL(l,s)::q -> if is_in_dpt s dpt vll then compile_var_decl_list q vll n dpt
        else begin
        write "\t subq $8, %rsp";
        compile_var_decl_list q ((s,n+1,dpt)::vll) (n+1) dpt
        end
    |CFUN(l,s,nvdl,lc)::q -> failwith "No Function Here"
  and compile_string sl = match sl with
    |[] -> ()
    |(s,n)::q -> begin
        write ((".LC" ^ (string_of_int n)) ^ ":");
        write (("\t .string \"" ^ (String.escaped s)) ^ "\"");
        compile_string q
          end
  and compile_code_list lcl fl vgl nlab vll n dpt sl nlabs = match lcl with
    |[] -> (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
    |(l,c)::q -> let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_code c fl vgl nlab vll n dpt sl nlabs) in compile_code_list q fl2 vgl2 nlab2 vll2 n2 dpt2 sl2 nlabs2
  and compile_code c fl vgl nlab vll n dpt sl nlabs = match c with
    |CBLOCK(vdl,lcl) -> let (vll2,n2) = compile_var_decl_list vdl vll n dpt in compile_code_list lcl fl vgl nlab vll2 n2 dpt sl nlabs
    |CEXPR(lexp) -> compile_expr lexp fl vgl nlab vll n dpt sl nlabs
    |CIF(lexp,(l1,c1),(l2,c2)) -> begin
       let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr lexp fl vgl nlab vll n dpt sl nlabs) in
       let res1 = (nlab2+1) in
       write "\t cmpq $0, %rax";
       write ("\t je .L" ^ (string_of_int nlab2));
       let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_code c1 fl2 vgl2 (nlab2 + 2) vll2 n2 (dpt+1) sl2 nlabs2) in
       write ("\t jmp .L" ^ (string_of_int res1));
       write ((".L" ^ (string_of_int nlab2)) ^ ":");
       let env4 = (compile_code c2 fl3 vgl3 nlab3 vll2 n3 (dpt+1) sl3 nlabs3) in
       write ((".L" ^ (string_of_int res1)) ^ ":");
       env4
       end
    |CWHILE(lexp,(l,c)) -> begin
        write ((".L" ^ (string_of_int nlab)) ^ ":");
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr lexp fl vgl (nlab+2) vll n dpt sl nlabs) in
        write "\t cmpq $0, %rax";
        write ("\t je .L" ^ (string_of_int (nlab+1)));
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_code c fl vgl2 nlab2 vll2 n2 (dpt+1) sl2 nlabs2) in
        write ("\t jmp .L" ^ (string_of_int nlab));
        write ((".L" ^ (string_of_int (nlab+1))) ^ ":");
        (fl3,vgl3,nlab3,vll2,n3,dpt,sl3,nlabs3)
        end
    |CRETURN(lexpo) -> match lexpo with
       |None ->  begin
           write ("\t jmp .R" ^ (fst_list fl));
           (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
           end
       |Some(e) -> begin
           let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = compile_expr e fl vgl nlab vll n dpt sl nlabs in
           write ("\t jmp .R" ^ (fst_list fl2));
           (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2)
           end
  and compile_expr (l,exp) fl vgl nlab vll n dpt sl nlabs = match exp with
    |VAR(s) -> begin
        write ((("\t movq " ^ (find_var s dpt vll))) ^ ", %rax");
        (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
        end
    |CST(x) -> begin
            write (("\t movq $" ^ (string_of_int x)) ^ ", %rax");
            (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
            end
    |STRING(s) -> begin
        write (("\t movq $.LC" ^ (string_of_int nlabs)) ^ ", %rax");
        (fl,vgl,nlab,vll,n,dpt,(s,nlabs)::sl,(nlabs+1))
        end
    |SET_VAR(s,el) -> begin
            let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el fl vgl nlab vll n dpt sl nlabs) in
            write ("\t movq %rax, " ^ (find_var s dpt2 vll));
            (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2)
            end
    |SET_ARRAY(s,el1,el2) -> begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
        write "\t movq %rax, %r10";
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = compile_expr el1 fl2 vgl2 nlab2 vll2 n2 dpt2 sl2 nlabs2 in
        write (("\t movq " ^ (find_var s dpt vll)) ^ ", %rbx");
        write "\t movq %r10, (%rbx,%rax,8)";
        write "\t movq %r10, %rax";
        (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3)
        end
    |CALL(f,lel) -> begin
        let nb = (max_2 ((len lel)-6) 0) mod 2 in
        if (nb + (n mod 2)) mod 2 = 1 then begin
        write "\t subq $8, %rsp";
        let (anb,fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = compile_call_args 0 (reverse lel) fl vgl nlab vll (n+1) dpt sl nlabs in
        let n3 = compile_call_move_args anb anb 1 in
        write "\t movq $0, %rax";
        write ("\t call " ^ f);
        if not (is_in f fl) then write "\t movslq %eax, %rax";
        write (("\t addq $" ^ (string_of_int (8*(n3-1)))) ^ ", %rsp");
        (fl2,vgl2,nlab2,vll2,n,dpt2,sl2,nlabs2)
        end
        else begin
        let (anb,fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = compile_call_args 0 (reverse lel) fl vgl nlab vll n dpt sl nlabs in
        let n3 = compile_call_move_args anb anb 1 in
        write "\t movq $0, %rax";
        write ("\t call " ^ f);
        if not (is_in f fl) then write "\t movslq %eax, %rax";
        write (("\t addq $" ^ (string_of_int (8*n3))) ^ ", %rsp");
        (fl2,vgl2,nlab2,vll2,n,dpt2,sl2,nlabs2)
        end
        end
    |OP1(mop,el) when mop = M_MINUS -> begin
        let env2  = (compile_expr el fl vgl nlab vll n dpt sl nlabs) in
        write "\t negq %rax";
        env2
        end
    |OP1(mop,el) when mop = M_NOT -> begin
        let env2 = (compile_expr el fl vgl nlab vll n dpt sl nlabs) in
        write "\t notq %rax";
        env2
        end
    |OP1(mop,(l,VAR(s))) when mop = M_POST_INC -> compile_po_var fl vgl nlab vll n dpt sl nlabs s "addq"
    |OP1(mop,(l,VAR(s))) when mop = M_POST_DEC -> compile_po_var fl vgl nlab vll n dpt sl nlabs s "subq"
    |OP1(mop,(l,VAR(s))) when mop = M_PRE_INC -> compile_pr_var fl vgl nlab vll n dpt sl nlabs s "addq"
    |OP1(mop,(l,VAR(s))) when mop = M_PRE_DEC -> compile_pr_var fl vgl nlab vll n dpt sl nlabs s "subq"
    |OP1(mop,(l,OP2(S_INDEX,(l1,VAR(s)),el))) when mop = M_POST_INC -> compile_po_tab fl vgl nlab vll n dpt sl nlabs s el "addq"
    |OP1(mop,(l,OP2(S_INDEX,(l1,VAR(s)),el))) when mop = M_POST_DEC -> compile_po_tab fl vgl nlab vll n dpt sl nlabs s el "subq"
    |OP1(mop,(l,OP2(S_INDEX,(l1,VAR(s)),el))) when mop = M_PRE_INC -> compile_pr_tab fl vgl nlab vll n dpt sl nlabs s el "addq"
    |OP1(mop,(l,OP2(S_INDEX,(l1,VAR(s)),el))) when mop = M_PRE_DEC -> compile_pr_tab fl vgl nlab vll n dpt sl nlabs s el "subq"
    |OP1(mop,el) -> failwith "Wrong use of INC or DEC"
    |OP2(bop,el1,el2) when bop = S_MUL ->  begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
        write "\t pushq %rax";
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el1 fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2) in
        write "\t imulq (%rsp), %rax";
        write "\t addq $8, %rsp";
        (fl3,vgl3,nlab3,vll3,n3-1,dpt3,sl3,nlabs3)
        end
    |OP2(bop,el1,el2) when bop = S_DIV -> begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
        write "\t pushq %rax";
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el1 fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2) in
        write "\t cqto";
        write "\t idivq (%rsp)";
        write "\t addq $8, %rsp";
        (fl3,vgl3,nlab3,vll3,n3-1,dpt3,sl3,nlabs3)
        end
    |OP2(bop,el1,el2) when bop = S_MOD ->  begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
        write "\t pushq %rax";
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el1 fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2) in
        write "\t cqto";
        write "\t idivq (%rsp)";
        write "\t movq %rdx, %rax";
        write "\t addq $8, %rsp";
        (fl3,vgl3,nlab3,vll3,n3-1,dpt3,sl3,nlabs3)
        end
   |OP2(bop,el1,el2) when bop = S_ADD -> begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
        write "\t pushq %rax";
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el1 fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2) in
        write "\t addq (%rsp), %rax";
        write "\t addq $8, %rsp";
        (fl3,vgl3,nlab3,vll3,n3-1,dpt3,sl3,nlabs3)
        end
    |OP2(bop,el1,el2) when bop = S_SUB -> compile_expr (l,OP2(S_ADD,el1,(l,OP1(M_MINUS,el2)))) fl vgl nlab vll n dpt sl nlabs
    |OP2(bop,el1,el2) when bop = S_INDEX -> begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
        write "\t pushq %rax";
        let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el1 fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2) in
        write "\t popq %rbx";
        write "\t movq (%rax,%rbx,8), %rax";
        (fl3,vgl3,nlab3,vll3,n,dpt3,sl3,nlabs3)
        end
    |OP2(bop,el1,el2) -> failwith "Wrong OP2"
    |CMP(cmp_op,el1,el2) when cmp_op = C_LT -> compile_cmp fl vgl nlab vll n dpt sl nlabs el1 el2 "jl"
    |CMP(cmp_op,el1,el2) when cmp_op = C_LE -> compile_cmp fl vgl nlab vll n dpt sl nlabs el1 el2 "jle"
    |CMP(cmp_op,el1,el2) when cmp_op = C_EQ -> compile_cmp fl vgl nlab vll n dpt sl nlabs el1 el2 "je"
    |CMP(cmp_op,el1,el2) -> failwith "Wrong CMP"
    |EIF(el1,el2,el3) -> begin
       let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el1 fl vgl nlab vll n dpt sl nlabs) in
       write "\t cmpq $0, %rax";
       write ("\t je .L" ^ (string_of_int nlab2));
       let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el2 fl2 vgl2 (nlab2 + 2) vll2 n2 dpt2 sl2 nlabs2) in
       write ("\t jmp .L" ^ (string_of_int (nlab2+1)));
       write ((".L" ^ (string_of_int nlab2)) ^ ":");
       let (fl4,vgl4,nlab4,vll4,n4,dpt4,sl4,nlabs4) = (compile_expr el3 fl3 vgl3 nlab3 vll3 n3 dpt3 sl3 nlabs3) in
       write ((".L" ^ (string_of_int (nlab2+1))) ^ ":");
       (fl4,vgl4,nlab4,vll4,n4,dpt4,sl4,nlabs4)
       end
    |ESEQ(lel) -> begin
        match lel with
        |[] -> (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
        |el::q -> begin
            let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = compile_expr el fl vgl nlab vll n dpt sl nlabs in
            compile_expr (l,ESEQ(q)) fl2 vgl2 nlab2 vll2 n2 dpt2 sl2 nlabs2
              end
              end
  and compile_po_var fl vgl nlab vll n dpt sl nlabs s op = begin
        write (("\t movq " ^ (find_var s dpt vll)) ^ ", %rax");
        write (("\t " ^ op) ^ " $1, " ^ (find_var s dpt vll));
        (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
      end
  and compile_pr_var fl vgl nlab vll n dpt sl nlabs s op = begin
        write ((("\t " ^ op) ^ " $1, ") ^ (find_var s dpt vll));
        write (("\t movq " ^ ((find_var s dpt vll))) ^ ", %rax");
        (fl,vgl,nlab,vll,n,dpt,sl,nlabs)
      end
  and compile_po_tab fl vgl nlab vll n dpt sl nlabs s el op = begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el fl vgl nlab vll n dpt sl nlab) in
        write ("\t pushq " ^ (find_var s dpt2 vll2));
        write "\t movq (%rsp), %rbx";
        write "\t movq (%rbx,%rax,8), %r10";
        write (("\t " ^ op) ^ " $1, (%rbx,%rax,8)");
        write "\t movq %r10, %rax";
        write "\t addq $8, %rsp";
        (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2)
        end
  and compile_pr_tab fl vgl nlab vll n dpt sl nlabs s el op = begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el fl vgl nlab vll n dpt sl nlab) in
        write (("\t pushq " ^ (find_var s dpt2 vll2)));
        write "\t movq (%rsp), %rbx";
        write (("\t " ^ op) ^ " $1, (%rbx,%rax,8)");
        write "\t movq (%rbx,%rax,8), %rax";
        write "\t addq $8, %rsp";
        (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2)
        end
  and compile_cmp fl vgl nlab vll n dpt sl nlabs el1 el2 s =
    let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el2 fl vgl nlab vll n dpt sl nlabs) in
    write "\t pushq %rax";
    let (fl3,vgl3,nlab3,vll3,n3,dpt3,sl3,nlabs3) = (compile_expr el1 fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2) in
    write "\t cmpq (%rsp), %rax";
    write ((("\t " ^ s) ^ " .L") ^ (string_of_int nlab3));
    write "\t movq $0, %rax";
    write ("\t jmp .L" ^ (string_of_int (nlab3+1)));
    write ((".L" ^ (string_of_int nlab3)) ^ ":");
    write "\t movq $1, %rax";
    write ((".L" ^ (string_of_int (nlab3+1))) ^ ":");
    write "\t addq $8, %rsp";
    (fl3,vgl3,nlab3+2,vll3,n3-1,dpt3,sl3,nlabs3)
  and compile_call_args anb lel fl vgl nlab vll n dpt sl nlabs = match lel with (*compile les arguments d'une fonctions lors d'un call et les met sur la pile*)
    |[] -> (anb,fl,vgl,nlab,vll,n,dpt,sl,nlabs)
    |el::q -> begin
        let (fl2,vgl2,nlab2,vll2,n2,dpt2,sl2,nlabs2) = (compile_expr el fl vgl nlab vll n dpt sl nlabs) in
        write "\t pushq %rax";
        compile_call_args (anb + 1) q fl2 vgl2 nlab2 vll2 (n2+1) dpt2 sl2 nlabs2
          end
  and compile_call_move_args anb n k = match (anb,k) with (* met les 6 premiers arguments d'une fonction qui ont étés placés sur la pile dans les registres d'appel*)
    |(0,_) -> n
    |(_,1) -> (write "\t popq %rdi" ; compile_call_move_args (anb-1) (n-1) (k+1))
    |(_,2) -> (write "\t popq %rsi" ; compile_call_move_args (anb-1) (n-1) (k+1))
    |(_,3) -> (write "\t popq %rdx" ; compile_call_move_args (anb-1) (n-1) (k+1))
    |(_,4) -> (write "\t popq %rcx" ; compile_call_move_args (anb-1) (n-1) (k+1))
    |(_,5) -> (write "\t popq %r8" ; compile_call_move_args (anb-1) (n-1) (k+1))
    |(_,6) -> (write "\t popq %r9" ; compile_call_move_args (anb-1) (n-1) (k+1))
    |_ -> n
in write "\t movq $16, %rax";
write "\t cqto";
write "\t idivq %rbp";
write "\t subq %rdx, %rbp";
compile_decl_list_ini vdl ["malloc";"calloc";"realloc";"exit";"fopen"] [] 1 0 0;
write "\t .ident	\"GCC: (Ubuntu 5.4.0-6ubuntu1~16.04.10) 5.4.0 20160609\"";
write "\t .section	.note.GNU-stack,\"\",@progbits"
