open Alcotest;

let () =
  run(
    "All_tests",
    [
      ("test_splay", Test_splay.splay_tests),
      ("test_validity", Test_validity.validity_tests),
    ],
  );
