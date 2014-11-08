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

;funcoes auxiliares
(defun preenche-ht-vars (vals lst-vars)
  ;ht e a hashtable
;  (let ((ht (make-hash-table))
(let (
        ;o i e o indice em que a variavel aparece na lista
        (i 0))
    (dolist (l lst-vars)
      ;inicializa-se a nil pois nao lhe esta atribuido nenhum valor
      ;o "i" e a posicao em que a variavel aparece na lista
      ;para caso seja preciso aceder ao dominio dessa variavel
     (setf (gethash l vals) (cons i nil))
     (incf i))))

(defun preenche-ht-rede (rede lst-restri)
;    (let ((ht (make-hash-table))
    (let (
          ;the pointer is used to avoid calling gethash twice
          (pointer))
          (dolist (lr lst-restri)
            (dolist (lv lr)
              (setf pointer (gethash lv rede))
              (setf pointer (cons lr pointer))))
            (flet ((f0 (key value) (setf (gethash key rede)(reverse value))))
                (maphash #'f0 rede))))



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
        ;;(restricoes lst-restri)
        ;valores de cada variavel
        ;(valores (preenche-ht-vars valores lst-vars))
        (valores (make-hash-table))
        ;rede de restricoes
        ;(rede (preenche-ht-rede rede lst-restri)))
        (rede (make-hash-table)))
    (progn (preenche-ht-vars valores lst-vars)
           (preenche-ht-rede rede lst-restri))
    (lambda (x &optional var val)
      (case x
        (a atribuidas)
        (na nao-atribuidas)
        (var variaveis)
        ;(dom-i (car (gethash var valores)))
        (dom-i (gethash var valores))
        (dom dominios)
        (res-v (gethash var rede))
        (val (cdr (gethash var valores)))
        (var-val (setf (gethash var valores) (cons (car (gethash var valores)) val)))
        (xpto valores)
        ))))

(defun psr-atribuicoes (psr)
  (funcall psr 'a))

(defun psr-variaveis-todas (psr)
  (funcall psr 'var))

(defun psr-variaveis-nao-atribuidas (psr)
  (funcall psr 'na))

(defun psr-variavel-valor (psr var)
  (funcall psr 'val var))

(defun psr-variavel-dominio (psr var)
  (let ((index (funcall psr 'dom-i var)))
    (nth index (funcall psr 'dom))))

; psr-variavel-
(defun psr-variavel-restricoes (psr var)
  (funcall psr 'res-v var))

(defun psr-adiciona-atribuicao! (psr var val)
  (funcall psr 'var-val var val))

(defun psr-remove-atribuicao! (psr var)
  (funcall psr 'var-val var nil))

(defun cenas (psr)
  (funcall psr 'xpto))
(load "exemplos.fas")
