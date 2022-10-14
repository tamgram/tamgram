type t = [
  | `Diffie_hellman
  | `Hashing
  | `Symmetric_encryption
  | `Asymmetric_encryption
  | `Signing
  | `Xor
  | `Multiset
]

let of_string (s : string) : t option =
  match s with
  | "diffie-hellman" -> Some `Diffie_hellman
  | "hashing" -> Some `Hashing
  | "symmetric-encryption" -> Some `Symmetric_encryption
  | "asymmetric-encryption" -> Some `Asymmetric_encryption
  | "signing" -> Some `Signing
  | "xor" -> Some `Xor
  | "multiset" -> Some `Multiset
  | _ -> None

let to_decls (t : t) : Tg_ast.decl list =
  match t with
  | `Diffie_hellman -> []
  | `Hashing ->
    [
      D_fun (Binding.make_untagged "h" 1)
    ]
  | `Symmetric_encryption ->
    [
      D_fun (Binding.make_untagged "senc" 2);
      D_fun (Binding.make_untagged "sdec" 2);
    ]
  | `Asymmetric_encryption ->
    [
      D_fun (Binding.make_untagged "aenc" 2);
      D_fun (Binding.make_untagged "adec" 2);
      D_fun (Binding.make_untagged "pk" 1);
    ]
  | `Signing ->
    [
      D_fun (Binding.make_untagged "sign" 2);
      D_fun (Binding.make_untagged "verify" 3);
      D_fun (Binding.make_untagged "true" 0);
    ]
  | `Xor ->
    [
      D_fun (Binding.make_untagged "zero" 0);
    ]
  | `Multiset -> []

let pp formatter (t : t) =
  match t with
  | `Diffie_hellman ->
    Fmt.pf formatter "diffie-hellman"
  | `Hashing ->
    Fmt.pf formatter "hashing"
  | `Symmetric_encryption ->
    Fmt.pf formatter "symmetric-encryption"
  | `Asymmetric_encryption ->
    Fmt.pf formatter "asymmetric-encryption"
  | `Signing ->
    Fmt.pf formatter "signing"
  | `Xor ->
    Fmt.pf formatter "xor"
  | `Multiset ->
    Fmt.pf formatter "multiset"

let to_string x =
  Fmt.str "%a" pp x
