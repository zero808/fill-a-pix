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
;K - variavel
;V - (posicao na lista de dominios . valor actual da variavel)
(defun preenche-ht-vars (vals lst-vars)
  (let ((i 0)) ;o i e o indice em que a variavel aparece na lista
    (dolist (l lst-vars)
      ;inicializa-se a nil pois nao lhe esta atribuido nenhum valor
      ;o "i" e a posicao em que a variavel aparece na lista
      ;para caso seja preciso aceder ao dominio dessa variavel
      (setf (gethash l vals) (cons i nil))
      (incf i))))

;K - variavel
;V - lista de variaveis que participam nas restricoes
(defun preenche-ht-rede (rede lst-restri)
  ;para cada restricao da lista de restricoes
  (dolist (lr lst-restri)
    ;para cada variavel da restricao
    (dolist (lv (restricao-variaveis lr))
      (setf (gethash lv rede) (cons lr (gethash lv rede)))))
  (flet ((f0 (key value) key (nreverse value)))
      (maphash #'f0 rede)))

(defun procura-atribuidas (vars vals)
  (let ((res nil))
    (dolist (temp vars (nreverse res))
      (if (cdr (gethash temp vals))
        (push (cons temp (cdr (gethash temp vals))) res)))))

(defun procura-nao-atribuidas (vars vals)
  (let ((res nil))
    (dolist (temp vars (nreverse res))
      (if (null (cdr (gethash temp vals)))
        (push temp res)))))

(defun consistente (restricoes psr)
  (do ((counter 0 (1+ counter))
       (result t)
       (element nil)
       (size (length restricoes)))
    ((or (= size counter) (not result)) (values result counter))
    (progn
      (setf element (restricao-funcao-validacao (nth counter restricoes)))
      (setf result (and result (funcall element psr))))))

(defun adiciona-valor! (valores var val)
  (setf (gethash var valores) (cons (car (gethash var valores)) val))
  )
  ;   se estivermos a adicionar o valor pela primeira vez
;  (if (null (member var atribuidas :test 'equal))
;    (values
;      ;adiciona a lista de atribuidas
;      (nconc atribuidas (list var))
;      ;e retira das nao atribuidas
;      (delete var nao-atribuidas :test 'equal))))
  ;e poe na hashtable o valor correcto

(defun remove-valor! (valores var)
  (setf (gethash var valores) (cons (car (gethash var valores)) nil))
  )
  ;(remove var atribuidas :test 'equal)
;  (values
;    (delete var atribuidas :test 'equal)
;    (nconc nao-atribuidas (list var))))

(defun procura-restricoes-comuns (restricoes var2)
  (let ((resultado nil))
    ;para cada restricao da var1 ve se var2 esta envolvido nela
    (dolist (restricao restricoes (nreverse resultado))
      (if (member var2 (restricao-variaveis restricao) :test 'equal)
        (push restricao resultado)))))

(defun testa-pacp (psr var novo )
  (let ((oldvalue (psr-variavel-valor psr var))
        (retorno nil))
    (psr-adiciona-atribuicao! psr var novo)
    (setf retorno (multiple-value-list (psr-variavel-consistente-p psr var)))
    (if (null oldvalue)
      (psr-remove-atribuicao! psr var)
      (psr-adiciona-atribuicao! psr var oldvalue))
    (values-list retorno)))

(defun testa-pacap (var1 val1 var2 val2 restricoes psr)
  (let ((antigo1 (psr-variavel-valor psr var1))
        (antigo2 (psr-variavel-valor psr var2))
        (retorno nil))

    (psr-adiciona-atribuicao! psr var1 val1)
    (psr-adiciona-atribuicao! psr var2 val2)
    (setf retorno (multiple-value-list (consistente restricoes psr)))
    (if (null antigo1)
      (psr-remove-atribuicao! psr var1)
      (psr-adiciona-atribuicao! psr var1 antigo1))
    (if (null antigo2)
      (psr-remove-atribuicao! psr var2)
      (psr-adiciona-atribuicao! psr var2 antigo2))
    (values-list retorno)))

; lista variaveis x lista dominios x lista restricoes -> PSR
(defun cria-psr (lst-vars lst-dominios lst-restri)
  (let (;(atribuidas nil) ;variaveis com valores atribuidos
        ;(nao-atribuidas (copy-list lst-vars)) ;variaveis que ainda nao tem valores atribuidos
        ;lista de todas as variaveis do problema
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
    ;(lambda (x &optional var1 val1 var2 val2 arg arg2)
    (lambda (psr &optional arg1 arg2 arg3 arg4 arg5 arg6)
      (case psr
        ;(pa atribuidas)
        (pa (procura-atribuidas lst-vars valores))
        ;(pvna (sort nao-atribuidas #'string-lessp))
        (pvna (procura-nao-atribuidas lst-vars valores))
        (pvt lst-vars)
        ;retorna o index em que a variavel se encontra
        (dom-i (car (gethash arg1 valores)))
        (dom dominios)
        ;devolve a lista de de restricoes que envolvem a variavel
        ;o car e o multiple-value-list e para evitar erros do gethash
        ;retornar dois valores
        (pvr (car (multiple-value-list (gethash arg1 rede))))
        ;retorna o valor atribuido a variavel
        (pvv (cdr (gethash arg1 valores)))
        ;troca o valor da variavel
        ; (paa (multiple-value-bind (a b) (corrige-valores valores atribuidas nao-atribuidas arg1 arg2)
        ;            (setf atribuidas a) (setf nao-atribuidas b)))
        (paa (adiciona-valor! valores arg1 arg2))
;               (if (or (not (null a)) (not (null b)))
;                 (progn
;                   (setf atribuidas a)
;                   (setf nao-atribuidas b)))))
        (pra (remove-valor! valores arg1))
;               (if (or (not (null a)) (not (null b)))
;                 (progn
;                   (setf atribuidas a)
;                   (setf nao-atribuidas b)))))
        ;verifica se algum valor de uma variavel esta a nil
        (comp (null (procura-nao-atribuidas lst-vars valores)))
        (consis (consistente restricoes arg1))
        (pvcp (consistente arg1 arg2))
        (pacp (testa-pacp arg1 arg2 arg3));var2 aqui sao as restricoes da variavel
        (pacap (testa-pacap arg1 arg2 arg3 arg4 arg5 arg6))
        ))))

(defun psr-atribuicoes (psr)
  (funcall psr 'pa))

(defun psr-variaveis-todas (psr)
  (funcall psr 'pvt))

(defun psr-variaveis-nao-atribuidas (psr)
  (funcall psr 'pvna))

(defun psr-variavel-valor (psr var)
  (funcall psr 'pvv var))

(defun psr-variavel-dominio (psr var)
  (let ((index (funcall psr 'dom-i var)))
    (if index (nth index (funcall psr 'dom)))))

; psr-variavel-
(defun psr-variavel-restricoes (psr var)
  (funcall psr 'pvr var))

(defun psr-adiciona-atribuicao! (psr var val)
  (funcall psr 'paa var val))

(defun psr-remove-atribuicao! (psr var)
  (funcall psr 'pra var nil))
  ; (funcall psr 'paa var nil))

(defun psr-altera-dominio! (psr var dom)
  (let ((index (funcall psr 'dom-i var)))
    (if index (setf (nth index (funcall psr 'dom)) dom))))

(defun psr-completo-p (psr)
  (funcall psr 'comp))

(defun psr-consistente-p (psr)
  (funcall psr 'consis psr))

(defun psr-variavel-consistente-p (psr variavel)
  (let ((res (psr-variavel-restricoes psr variavel)))
    (funcall psr 'pvcp res psr)))

(defun psr-atribuicao-consistente-p (psr variavel valor)
;  (let ((res (psr-variavel-restricoes psr variavel)))
;    (funcall psr 'pacp variavel valor res psr)))
    (funcall psr 'pacp psr variavel valor))

(defun psr-atribuicoes-consistentes-arco-p (psr var1 val1 var2 val2)
;  (funcall psr 'pacap var1 val1 var2 val2 (remove-duplicates
;                                            (append (psr-variavel-restricoes psr var1)
;                                                    (psr-variavel-restricoes psr var2))
;                                            :test 'eq :from-end t) psr))
(funcall psr 'pacap var1 val1 var2 val2 (procura-restricoes-comuns (psr-variavel-restricoes psr var1)
                                                                   var2) psr))


;parte 2.2.1
;(defun fill-a-pix->psr (arr))

;(defun psr->fill-a-pix (psr linhas colunas))

;parte 2.2.2
;(defun procura-retrocesso-simples (psr))

;(defun resolve-simples (arr))


;this way it works in whatever implementation
#+clisp (load "exemplos.fas")
#+sbcl (load "exemplos.fasl")
