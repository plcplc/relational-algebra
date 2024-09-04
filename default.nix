{ mkDerivation, aeson, base, bytestring, containers, data-has
, directory, generics-sop, lens, lib, mtl, pretty-show, profunctors
, sqlite-simple, stm, template-haskell, text, time, transformers
, unliftio-core, uuid, uuid-types
}:
mkDerivation {
  pname = "relational-algebra";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    aeson base bytestring containers data-has directory generics-sop
    lens mtl pretty-show profunctors sqlite-simple stm template-haskell
    text time transformers unliftio-core uuid uuid-types
  ];
  description = "An embedded DSL for relational algebra";
  license = lib.licenses.agpl3Plus;
}
