;(library
; (name jsooexp_exceptions)
; (modules exceptions)
; (libraries js_of_ocaml_compiler unix str jsoo_compiler_expect_tests_helper)
; (inline_tests
;  (flags -allow-output-patterns)
;  (deps
;   (file ../../../compiler/bin-js_of_ocaml/js_of_ocaml.exe)
;   (file ../../../compiler/bin-jsoo_minify/jsoo_minify.exe)))
; (flags (:standard -open Jsoo_compiler_expect_tests_helper))
; (preprocess
;  (pps ppx_expect)))
;
;(library
; (name jsooexp_array_access)
; (modules array_access)
; (libraries js_of_ocaml_compiler unix str jsoo_compiler_expect_tests_helper)
; (inline_tests
;  (flags -allow-output-patterns)
;  (deps
;   (file ../../../compiler/bin-js_of_ocaml/js_of_ocaml.exe)
;   (file ../../../compiler/bin-jsoo_minify/jsoo_minify.exe)))
; (flags (:standard -open Jsoo_compiler_expect_tests_helper))
; (preprocess
;  (pps ppx_expect)))

(library
 (name jsooexp_effects_simple)
 (modules effects_simple)
 (libraries js_of_ocaml_compiler unix str jsoo_compiler_expect_tests_helper)
 (inline_tests
  (flags -allow-output-patterns)
  (deps
   (file ../../../compiler/bin-js_of_ocaml/js_of_ocaml.exe)
   (file ../../../compiler/bin-jsoo_minify/jsoo_minify.exe)))
 (flags (:standard -open Jsoo_compiler_expect_tests_helper))
 (preprocess
  (pps ppx_expect)))
