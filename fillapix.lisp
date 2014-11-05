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
(defun preenche-ht (lst-vars)
  ;ht e a hashtable
  (let ((ht (make-hash-table))
        ;o i e o indice em que a variavel aparece na lista
        (i 0))
    (dolist (l lst-vars)
      ;inicializa-se a nil pois nao lhe esta atribuido nenhum valor
     (setf (gethash l ht) (cons i nil)))
    ht))

; lista variaveis x lista dominios x lista restricoes -> PSR
(defun cria-psr (lst-vars lst-dominios lst-restri)
  (let ((atribuidas nil) ;variaveis com valores atribuidos
        (nao-atribuidas nil) ;variaveis que ainda nao tem valores atribuidos
        ;lista de todas as variaveis do problema
        ;NOTE: Isto nao e redundante?
        (variaveis lst-vars)
        ;os dominios de cada variavel
        (dominios lst-dominios)
        ;as restricoes do problema
        (restricoes lst-restri)
        (valores (preenche-ht lst-vars)))
    (lambda (x)
      (case x
        (a atribuidas)
        (na nao-atribuidas)
        (var variaveis)
        (dom dominios)
        (res restricoes)
        (val valores)))))

(defun psr-atribuicoes (psr)
  (funcall psr 'a))

(defun psr-variaveis-todas (psr)
  (funcall psr 'var))

(defun psr-variaveis-nao-atribuidas (psr)
  (funcall psr 'na))

(defun psr-variavel-valor (psr)
  (funcall psr 'na))
