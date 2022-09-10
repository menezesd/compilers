(* CS 515  *)
(* Author: Prof Santosh Nagarakatte, based on Prof. Steve Zdancewic's code *)

(* A compilation unit is a collection of labeled, global data *)
(* It will be processed by "as" -- the assembler *)

(* Global Data Values *)

type global = 
 | GStringz of string                         (* A null-terminated string *)
 | GSafeStringz of string                     (* A null-terminated string prefixed by its length *)
 | GLabelOffset of X86simplified.lbl * int32  (* A label with offset *)
 | GLabels of X86simplified.lbl list         (* A list of lablels *)
 | GInt32 of int32                            (* A literal [int32] value *)
 | GZero of int                               (* Zeroed memory of size n bytes *)
 | GExtern                                    (* Defined outside this compilation unit *)

type global_data = {
   link : bool;                  (* Determines whether this label is exposed outside the compilation unit *)               
   label: X86simplified.lbl;     (* The label of this data *)
   value: global;                (* The value stored at this label *)
}

(* Quotes a string for printing, appends the null terminator *)

let quote_asm_string s = 
    let outbuf = Buffer.create (String.length s) in 
    Buffer.add_char outbuf '\"';
    String.iter (function 
    | 'n'  -> Buffer.add_string outbuf "\\n"
    | '\"' -> Buffer.add_string outbuf "\\\""
    | '\\' -> Buffer.add_string outbuf "\\\\"
    | '\t' -> Buffer.add_string outbuf "\\t"
    | c    -> Buffer.add_char outbuf c
    ) s;
    Buffer.add_string outbuf "\\0\"";
    Buffer.contents outbuf

(* .globl <label> and .global <label> are both directives allowed by the assembler *)
let string_of_global_data d = 
  let maybe_global = if (d.link || d.value = GExtern) then (
      ".globl " ^ (X86simplified.string_of_lbl d.label) ^ "\n"
      ) else "" in 
      let data_defn = 
        match d.value with
        | GSafeStringz s -> "\t.long " ^ (string_of_int (String.length s)) ^
            "\n\t.ascii " ^ (quote_asm_string s)
        | GStringz s  ->  "\t.ascii " ^ (quote_asm_string s)
        | GLabelOffset (l, i) -> "\t.long " ^ (X86simplified.string_of_lbl l) ^ " + " ^
          (Int32.to_string i)
        | GLabels lst -> List.fold_left 
            (fun s -> fun l -> s ^ "\t.long " ^ X86simplified.string_of_lbl l ^ "\n" ) "" lst
        | GInt32 v -> "\t.long " ^ (Int32.to_string v)
        | GZero z  -> "\t.zero " ^ (string_of_int z)
        | GExtern  -> ""

      in 
         maybe_global ^
          (if (d.value <> GExtern) then 
            (X86simplified.string_of_lbl d.label) ^ ":\n" ^ data_defn ^ "\n"
           else "")

(* Compilation Units are Lists of Components *)
type component = 
 | Code of X86simplified.insn_block
 | Data of global_data

type cunit = component list

let mode_data = "\t.data\n"
let mode_text = "\t.text\n"

let serialize_cunit (cu:cunit) (printfn: string -> unit) = 
  (* x86 does not generally require alignment on natural boundaries
   * (i16: even-numbered addresses; i32: divisible by 4; i64: divisible by 8)
   * but the performance of programs will improve if this alignment is
   * maintained wherever possible. The processor may require two
   * memory accesses to read a single unaligned memory address. (see: 
   * IA-32 Intel Architecture Software Developer's Manual, Volume 1, 4-2) *)
  
  printfn "\t.align 4\n";
  ignore (List.fold_left 
           (fun mode ni -> 
               let mode' = 
                 match ni with 
                 | Code c -> 
                      (if mode <> mode_text then printfn mode_text);
                       X86simplified.serialize_insn_block c printfn;
                       mode_text
                 | Data d -> 
                     (if mode <> mode_data then printfn mode_data);
                     printfn (string_of_global_data d);
                     mode_data
                in mode'
           ) "" cu )

let string_of_cunit cu = 
   let b = Buffer.create 256 in 
     (serialize_cunit cu (Buffer.add_string b));
     Buffer.contents b

let output_cunit (cu:cunit) (oc:out_channel) = 
   serialize_cunit cu (output_string oc)

    
