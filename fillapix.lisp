; vim: set ft=lisp:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Alameda
; Grupo 42
;
; Duarte Barreira   n 64752
; Ricardo Coelho    n 64831
; Pedro Baptista    n 67056
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Tipo restricao
; variavel e uma string
; dominio e representado por uma lista de valores possiveis
; ex: a lista (0 1) representa um dominio com 2 valores possiveis para
; essa variavel.

; cria-restricao: lista de variaveis x predicado -> restricao
(defun cria-restricao (lst-var pred)
  (list lst-var pred))


; restricao-variaveis: restricao -> lista de variaveis
(defun restricao-variaveis (restricao)
  (first restricao))

; restricao-funcao-validacao: restricao -> predicado
(defun restricao-funcao-validacao (restricao)
  (second restricao))

; Tipo PSR

;funcoes auxiliares
(defun preenche-ht-vars (vals lst-vars)
  (let ((i 0)) ;o i e o indice em que a variavel aparece na lista
    (dolist (l lst-vars)
      ;inicializa-se a nil pois nao lhe esta atribuido nenhum valor
      ;o "i" e a posicao em que a variavel aparece na lista
      ;para caso seja preciso aceder ao dominio dessa variavel
      (setf (gethash l vals) (cons i nil))
      (incf i))))

(defun preenche-ht-rede (rede lst-restri)
  ;para cada restricao da lista de restricoes
  (dolist (lr lst-restri)
    ;para cada variavel da restricao
    (dolist (lv (restricao-variaveis lr))
      (setf (gethash lv rede) (cons lr (gethash lv rede)))))
  (flet ((f0 (key value) key (nreverse value)))
      (maphash #'f0 rede)))

(defun busca-valores (valores lista-vars)
  (let ((l nil))
    (dolist (lv lista-vars)
      ;(setf l (cons (second (gethash lv valores)) l)))
      (setf l (cons (cdr (gethash lv valores)) l)))
    (nreverse l)))

(defun val-nil (l)
  (do ((i 0 (+ 1 i))
       (size (length l))
       (res nil))
      ((or res (= i size)) res)
    (if (null (nth i l))
        (setf res t))))

(defun consistente (valores restricoes psr)
  (do ((counter 0 (+ 1 counter))
       (flag t)
       (l nil)
       (i 0 (+ 1 i)) ;; provavelmente nao necessario, igual ao counter
       (restri-i nil)
       (size (length restricoes)))
     ((= size i) (values flag counter)) ;; condicao de paragem e resultado devolvido
   (progn
     (setf restri-i (nth i restricoes))
     (setf l (busca-valores valores (restricao-variaveis restri-i)))
     (if (not (val-nil l))
         (setf flag (and (mapcar (restricao-funcao-validacao restri-i)
                                 ;(busca-valores valores (restricao-variaveis restri-i)))
                                 psr)
                          flag))))))

(defun corrige-valores (valores atribuidas nao-atribuidas var val)
  (setf (gethash var valores) (cons (car (gethash var valores)) val))
  (if (null val)
    ;queremos remover
    (values
      (remove var atribuidas :test 'equal)
      (if (null (find var nao-atribuidas :test 'equal))
        (append nao-atribuidas (list var))
        nao-atribuidas))
    ;queremos alterar o valor
    (values
      ;para testar se e a primeira vez que fazemos uma atribuicao
      ;ou se estamos a alterar um valor existente
      (if (null (find var atribuidas :test 'equal))
        (append atribuidas (list var))
        atribuidas)
      (remove var nao-atribuidas :test 'equal))))

(defun testa-pacp (valores var novo restricoes psr)
  (let ((antigo (cdr (gethash var valores)))
        (retorno nil))
    ;alteramos isto manualmente para nao modificar as listas de atribuidos e nao
    ;atribuidos
    (setf (cdr (gethash var valores)) novo)
    (setf retorno (multiple-value-list (consistente valores restricoes psr)))
    (setf (cdr (gethash var valores)) antigo)
    (values-list retorno)))

(defun testa-pacap (valores var1 val1 var2 val2 restricoes psr)
  (let ((antigo1 (cdr (gethash var1 valores)))
        (antigo2 (cdr (gethash var2 valores)))
        (retorno nil))
    ;alteramos isto manualmente para nao modificar as listas de atribuidos e nao
    ;atribuidos
    (setf (cdr (gethash var1 valores)) val1)
    (setf (cdr (gethash var2 valores)) val2)
    (setf retorno (multiple-value-list (consistente valores restricoes psr)))
    (setf (cdr (gethash var1 valores)) antigo1)
    (setf (cdr (gethash var2 valores)) antigo2)
    (values-list retorno)))

; lista variaveis x lista dominios x lista restricoes -> PSR
(defun cria-psr (lst-vars lst-dominios lst-restri)
  (let ((atribuidas nil) ;variaveis com valores atribuidos
        (nao-atribuidas (copy-list lst-vars)) ;variaveis que ainda nao tem valores atribuidos
        ;lista de todas as variaveis do problema
        ;NOTE: Isto nao e redundante?
        ;(variaveis lst-vars)
        ;os dominios de cada variavel
        (dominios lst-dominios)
        ;as restricoes do problema
        (restricoes lst-restri)
        ;valores de cada variavel
        (valores (make-hash-table :test 'equal))
        ;rede de restricoes
        (rede (make-hash-table :test 'equal))
        ;flag para comparacoes
        ;(flag t)
        )
    (progn (preenche-ht-vars valores lst-vars)
           (preenche-ht-rede rede lst-restri))
    (lambda (x &optional var1 val1 var2 val2 arg arg2)
      (case x
        (a atribuidas)
        (na nao-atribuidas)
        (var lst-vars)
        ;retorna o index em que a variavel se encontra
        (dom-i (car (gethash var1 valores)))
        (dom dominios)
        ;devolve a lista de de restricoes que envolvem a variavel
        ;o car e o multiple-value-list e para evitar erros do gethash
        ;retornar dois valores
        (res-v (car (multiple-value-list (gethash var1 rede))))
        ;retorna o valor atribuido a variavel
        (val (cdr (gethash var1 valores)))
        ;troca o valor da variavel
        (var-val (multiple-value-bind (a b) (corrige-valores valores atribuidas nao-atribuidas var1 val1)
                   (setf atribuidas a) (setf nao-atribuidas b)))
        ;verifica se algum valor de uma variavel esta a nil
        ;(comp (progn (maphash #'(lambda (k v) k (setf flag (and (notany #'null (cdr v)) flag))) valores) flag))
        (comp (null nao-atribuidas))
        (consis (consistente valores restricoes var1))
;        (vcp (values t 0));yeah fix this...
        (vcp (consistente valores var1 val1)); var1 in this case is not a variable
        (pacp (testa-pacp valores var1 val1 var2 arg));var2 aqui sao as restricoes da variavel
        (pacap (testa-pacap valores var1 val1 var2 val2 arg arg2))
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
    (if index (nth index (funcall psr 'dom)))))

; psr-variavel-
(defun psr-variavel-restricoes (psr var)
  (funcall psr 'res-v var))

(defun psr-adiciona-atribuicao! (psr var val)
  (funcall psr 'var-val var val))

(defun psr-remove-atribuicao! (psr var)
  (funcall psr 'var-val var nil))

(defun psr-altera-dominio! (psr var dom)
  (let ((index (funcall psr 'dom-i var)))
    (if index (setf (nth index (funcall psr 'dom)) dom))))

(defun psr-completo-p (psr)
  (funcall psr 'comp))

(defun psr-consistente-p (psr)
  (funcall psr 'consis psr))

(defun psr-variavel-consistente-p (psr variavel)
  (let ((res (psr-variavel-restricoes psr variavel)))
    (funcall psr 'vcp res psr)))

(defun psr-atribuicao-consistente-p (psr variavel valor)
  (let ((res (psr-variavel-restricoes psr variavel)))
    (funcall psr 'pacp variavel valor res psr)))

(defun psr-atribuicoes-consistentes-arco-p (psr var1 val1 var2 val2)
  (funcall psr 'pacap var1 val1 var2 val2 (remove-duplicates
                                            (append (psr-variavel-restricoes psr var1)
                                                    (psr-variavel-restricoes psr var2))
                                            :test 'eq) psr))

;parte 2.2.1
;(defun fill-a-pix->psr (arr))

;(defun psr->fill-a-pix (psr linhas colunas))

;parte 2.2.2
;(defun procura-retrocesso-simples (psr))

;(defun resolve-simples (arr))


;this way it works in whatever implementation
#+clisp (load "exemplos.fas")
#+sbcl (load "exemplos.fasl")
