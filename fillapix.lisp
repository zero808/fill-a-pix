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
;
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
    (setf l (cons (second (gethash lv valores)) l)))
  (nreverse l)))

(defun val-nil (l)
  (let ((res nil))
    (dolist (valor l) res
      (if (equal valor nil)
        (progn (setf res t)
            (return))))))

(defun consistente (valores restricoes)
  (let ((counter 0)
        (flag t)
        (l nil))
    (dolist (lr restricoes) (values flag counter)
      (if flag
        (progn
          (setf l (busca-valores valores (restricao-variaveis lr)))
          (if (not (val-nil l))
            (setf flag (and (mapcar (restricao-funcao-validacao lr)
                                    (busca-valores valores (restricao-variaveis lr)))
                            flag)))
          (incf counter))
        (return)))))

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
        ;valores de cada variavel
        (valores (make-hash-table :test 'equal))
        ;rede de restricoes
        (rede (make-hash-table :test 'equal))
        ;flag para comparacoes
        (flag t)
        )
    (progn (preenche-ht-vars valores lst-vars)
           (preenche-ht-rede rede lst-restri))
    (lambda (x &optional var val)
      (case x
        (a atribuidas)
        (na nao-atribuidas)
        (var variaveis)
        ;retorna o index em que a variavel se encontra
        (dom-i (car (gethash var valores)))
        (dom dominios)
        ;devolve a lista de de restricoes que envolvem a variavel
        ;o car e o multiple-value-list e para evitar erros do gethash
        ;retornar dois valores
        (res-v (car (multiple-value-list (gethash var rede))))
        ;retorna o valor atribuido a variavel
        (val (cdr (gethash var valores)))
        ;troca o valor da variavel
        (var-val (setf (gethash var valores) (cons (car (gethash var valores)) val)))
        ;verifica se algum valor de uma variavel esta a nil
        (comp (progn (maphash #'(lambda (k v) k (setf flag (and (notany #'null (cdr v) flag)))) valores) flag))
        (consis (consistente valores restricoes))
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

(defun psr-altera-dominio! (psr var dom)
  (let ((index (funcall psr 'dom-i var)))
    (setf (nth index (funcall psr 'dom)) dom)))

(defun psr-completo-p (psr)
  (funcall psr 'comp))

(defun psr-consistente-p (psr)
  (funcall psr 'consis))

(load "exemplos.fas")
