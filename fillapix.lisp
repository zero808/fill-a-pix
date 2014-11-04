;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Alameda
; Grupo 42
;
; Duarte Barreira   nº 64752
; Ricardo Coelho    nº 64831
; Pedro Baptista    nº 67056
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Tipo restricao
; variavel e uma string
; dominio e representado por uma lista de valores possiveis
; ex: a lista (0 1) representa um dominio com 2 valores possiveis para
; essa variavel.

; cria-restricao: lista de variáveis x predicado -> restricao
(defun cria-restricao (lst-var pred)
  (list lst-var pred))


; restricao-variaveis: restricao -> lista de variaveis
(defun restricao-variaveis (restricao)
  (first restricao))
;
; restricao-funcao-validacao: restricao -> predicado
(defun restricao-funcao-validacao (restricao)
  (second restricao))

; Tipo PSR

;e mais facil usar uma estrutura para aceder facilmente aos campos
;em vez de andar a passar argumentos e consoante o argumento devolver
;um certo campo
(defstruct psr
  ;variaveis com valores atribuidos
  (atribuidas nil)
  ;variaveis que ainda nao tem valores atribuidos
  (nao-atribuidas nil)
  ;lista de todas as variaveis do problema
  ;NOTE: Isto nao e redundante?
  (variaveis nil)
  ;os dominios de cada variavel
  (dominios nil)
  ;as restricoes do problema
  (restricoes nil))

; lista variaveis x lista dominios x lista restricoes -> PSR
(defun cria-psr (lst-vars lst-dominios lst-restri)
  ; (let ((atribuidas nil) ;variaveis com valores atribuidos
  ;       (nao-atribuidas nil)) ;variaveis que ainda nao tem valores atribuidos
  (let (psr (make-psr :variaveis lst-vars :dominios lst-dominios :restricoes lst-restri)))
    ;continuamos a ter que passar o psr de alguma maneira...))
