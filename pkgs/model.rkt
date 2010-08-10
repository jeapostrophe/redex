#lang racket
(require redex)

(define-syntax-rule (test-term-equal t_0 t_1)
  (test-equal (term t_0) (term t_1)))
(define-syntax-rule (test-term-pattern p t)
  (test-predicate (redex-match lang p) (term t)))

(define-language lang
  ; Some globals
  [id variable-not-otherwise-mentioned]
  
  ; A simple filesystem is a tree of files
  [dir (node ...)]
  [node [id -> file]
        [id -> dir]]
  [fs dir]
  [path (id ...)]
  
  ; A package database is a list of packages
  [db (pkg-info ...)]
  
  ; A package info is a name, version, deps, provides, and a list of paths that were installed
  [pkg-info (pkg-name version (dep ...) (provide ...) (path ...))]
  [pkg-name string]
  ; ... A version is a major and minor number
  [version (number number)]
  ; ... A version spec treats a number as either a wildcard or a number
  [version-spec (num num)]
  [num *
       number]
  [dep (pkg-name = version-spec)]
  [provide path]
  
  ; A package is a package info and a filesystem
  [package (pkg-info fs)]
  
  ; A system is a a package database and a filesystem
  [system (db fs)]
  
  ; A file is a module
  [file mod]
  ; A module is just a require
  [mod (require ...)]
  ; A require is an absolute path
  [require path]
  
  ; An ans
  [ans (path ...)
       error])

;; Primary functions

(define system_0
  (term (() 
         ([main -> ()]
          [hidden -> ()]))))

(test-term-pattern system ,system_0)

(define-metafunction lang
  run : system require -> ans
  [(run system require)
   ; XXX
   ()])

(define-metafunction lang
  install : system package -> system
  [(install system package)
   ; XXX
   system])

(define-metafunction lang
  uninstall : system pkg-name version -> system
  [(uninstall system pkg-name version)
   ; XXX
   system])

(define-metafunction lang
  seal : system pkg-name version -> system
  [(seal system pkg-name version)
   ; XXX
   system])

;; Helper functions

(define-metafunction lang
  install* : system package ... -> system
  [(install* system)
   system]
  [(install* system package_0 package_n ...)
   (install* (install system package_0) package_n ...)])

(test-term-equal (install* ,system_0) ,system_0)
; XXX more tests

;; Properties
(define property-attempts 100)

(redex-check lang (system_0 package)
             (let ([system_1 (term (install system_0 package))])
               (equal? (term ,system_1) (term (install ,system_1 package))))
             #:attempts property-attempts
             #:source install)

; For all install-paths from system_0 to system_n, every module is associated with a single package
; For all install-paths from system_0 to system_n, every module can run without errors and will never refer to a non-provided path from another package
; XXX More properties

(test-results)