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


; recebe a posicao num array de (n * m) e identifica o seu numero de posicao entre 0 a ((n * m) - 1)
; calculado atrave's de (tamanho-coluna * linha) + numero-coluna
; exemplo: posicao (3,4) num array 5*5; linha 3, coluna 4
;          (5 * 3) + 4 = 15 + 4 = 19
;          elemento 19
; argumentos
; i - inteiro que identifica a linha
; j - inteiro que identifica a coluna
; dimensao - lista de dois elementos com o tamanho do array
(defun identifica-numero-variavel (i j dimensao)
  (let ((tamanho-coluna (second dimensao)))
      (+ (* tamanho-coluna i) j)))

; recebe um array e cria uma lista de variaveis com todos os elementos do array
; usa a funcao identifica-numero-variavel para dar um nome unico a cada variavel
; coincide que o numero da variavel vai ser tambem a posicao na lista de dominios
(defun cria-lista-variaveis (array)
  (let ((tamanho-linha (first (array-dimensions array))) ; i max
		(tamanho-coluna (second (array-dimensions array))) ; j max
        (resultado nil))
    (do ((i 0 (+ i 1)))
      ((= i tamanho-linha) (nreverse resultado)) ; devolve-se a lista resultado revertida
     (do ((j 0 (+ j 1)))
       ((= j tamanho-coluna))
      (push (write-to-string (identifica-numero-variavel i j (list tamanho-linha tamanho-coluna)))
            resultado))))) ; adicionar cada nome de variavel 'a lista

; devolve T se numero esta entre numero-minimo e numero-maximo
(defun numero-valido (numero numero-minimo numero-maximo)
  (and (>= numero numero-minimo)
       (<= numero numero-maximo))) ;

; recebe uma posicao num array e devolve uma lista de posicoes adjacentes
(defun lista-adjacentes (i j dimensao)
  (let ((tamanho-linha (first dimensao)) ; i max
		(tamanho-coluna (second dimensao)) ; j max
        (resultado nil)
        (lista-auxiliar nil))
      (setf lista-auxiliar (list (cons (- i 1) (- j 1))  ; todas as posicoes adjacentes possiveis
                                 (cons (- i 1) j)
                                 (cons (- i 1) (+ j 1))
                                 (cons i (- j 1))
                                 (cons i j)
                                 (cons i (+ j 1))
                                 (cons (+ i 1) (- j 1))
                                 (cons (+ i 1) j)
                                 (cons (+ i 1) (+ j 1))))
      (dolist (elemento lista-auxiliar (nreverse resultado))
        (if (and (numero-valido (car elemento) 0 (- tamanho-linha 1))  ; verificar se o par de posicao e' valido
                 (numero-valido (cdr elemento) 0 (- tamanho-coluna 1)))
            (push elemento resultado))))) ; se for valido, adiciona-se a lista de posicoes adjacentes



(defun faz-restricao (posicoes-adjacentes valor tamanho)
  (let ((lista-variaveis nil)
        (predicado nil))
    (dolist (elemento posicoes-adjacentes)
      (push (write-to-string (identifica-numero-variavel (car elemento) (cdr elemento) tamanho)) lista-variaveis))
    (setf lista-variaveis (nreverse lista-variaveis))
    (cond
        ((= (length lista-variaveis) 9) (setf predicado #'(lambda (psr) (let ((el0 (psr-variavel-valor psr (nth 0 lista-variaveis)))
                                                                              (el1 (psr-variavel-valor psr (nth 1 lista-variaveis)))
                                                                              (el2 (psr-variavel-valor psr (nth 2 lista-variaveis)))
                                                                              (el3 (psr-variavel-valor psr (nth 3 lista-variaveis)))                                                                                           
                                                                              (el4 (psr-variavel-valor psr (nth 4 lista-variaveis)))
                                                                              (el5 (psr-variavel-valor psr (nth 5 lista-variaveis)))
                                                                              (el6 (psr-variavel-valor psr (nth 6 lista-variaveis)))
                                                                              (el7 (psr-variavel-valor psr (nth 7 lista-variaveis)))
                                                                              (el8 (psr-variavel-valor psr (nth 8 lista-variaveis))))
                                                                                  ;; alguma outra maneira de fazer isto?
                                                                                  
                                                                           ;; se o numero de 0s nas variaveis tem de ser inferior ou igual a 9 - valor
                                                                           ;; se nao, mesmo que algumas variaveis nao estejam atribuidas
                                                                           ;; e' possivel inferir que este predicado nao e' verdade.   
                                                                          (if (> (count 0 (list el0 el1 el2 el3 el4 el5 el6 el7 el8)) (- 9 valor))
                                                                              nil
                                                                              (if (and el0 el1 el2 el3 el4 el5 el6 el7 el8) (= (+ el0 el1 el2 el3 el4 el5 el6 el7 el8) valor) T))))))
                                                                              
        ((= (length lista-variaveis) 6) (setf predicado #'(lambda (psr) (let ((el0 (psr-variavel-valor psr (nth 0 lista-variaveis)))
                                                                                 (el1 (psr-variavel-valor psr (nth 1 lista-variaveis)))
                                                                                 (el2 (psr-variavel-valor psr (nth 2 lista-variaveis)))
                                                                                 (el3 (psr-variavel-valor psr (nth 3 lista-variaveis)))                                                                                           
                                                                                 (el4 (psr-variavel-valor psr (nth 4 lista-variaveis)))
                                                                                 (el5 (psr-variavel-valor psr (nth 5 lista-variaveis))))
                                                                             (if (> (count 0 (list el0 el1 el2 el3 el4 el5)) (- 6 valor))
                                                                                 nil
                                                                                 (if (and el0 el1 el2 el3 el4 el5) (= (+ el0 el1 el2 el3 el4 el5) valor) T))))))
        
        ((= (length lista-variaveis) 4) (setf predicado #'(lambda (psr) (let ((el0 (psr-variavel-valor psr (nth 0 lista-variaveis)))
                                                                              (el1 (psr-variavel-valor psr (nth 1 lista-variaveis)))
                                                                              (el2 (psr-variavel-valor psr (nth 2 lista-variaveis)))
                                                                              (el3 (psr-variavel-valor psr (nth 3 lista-variaveis))))                                                                                           
                                                                           (if (> (count 0 (list el0 el1 el2 el3)) (- 4 valor))
                                                                               nil
																		       (if (and el0 el1 el2 el3) (= (+ el0 el1 el2 el3) valor) T)))))))
     (cria-restricao lista-variaveis predicado)))

(defun cria-dominio-restricao (array)
  (let* ((tamanho-linha (first (array-dimensions array)))
         (tamanho-coluna (second (array-dimensions array)))
         (dominio (make-list (* tamanho-linha tamanho-coluna) :initial-element (list 0))) ; o dominio de todas as variaveis e' por definicao 0. Pode ser 0 e 1 ou apenas 1
         (restricoes nil))
     (do ((i 0 (+ i 1)))
       ((= i tamanho-linha))
      (do ((j 0 (+ j 1)))
        ((= j tamanho-coluna))
       (if (numberp (aref array i j)) ; se encontrar um numero, e' necessario mudar os dominios das variaveis adjacentes e criar uma restricao
           (progn
             (let ((posicoes-adjacentes (lista-adjacentes i j (list tamanho-linha tamanho-coluna))))
               ;; comentado por nao dar resultados esperados: vai-se entao criar um predicado para fazer a soma de todos os valores a dar 9 em vez de simplesmente contar o dominio destas variaveis a 1.
               ;(if (= (aref array i j) 9) ; implica que todas as variaveis 'a volta sao 1. Nao e' necessario predicado, apenas dominio de 1 para todas as variaveis adjacentes
                ;   (dolist (elemento posicoes-adjacentes)
                 ;    (setf (nth (identifica-numero-variavel (car elemento) (cdr elemento) (list tamanho-linha tamanho-coluna)) dominio) (list 1))) ; de todas as variaveis adjacentes, muda o dominio para 1     
                 ; se o numero for menor que 9, o dominio destas variaveis e' (0 1), no entanto algumas destas variaveis ja podem ter tido o seu dominio mudado para 1, nesse caso nao pretendemos alterar
                 ; no caso de ter sido mudado para (0 1), tambem nao e' necessario mudar.
                 ; e' preciso apenas mudar no caso do dominio ser 0.
                    (dolist (elemento posicoes-adjacentes)  ; para cada posicao, vai-se mudar o dominio para (0 1)
                            (let ((numero-variavel (identifica-numero-variavel (car elemento) (cdr elemento) (list tamanho-linha tamanho-coluna))))
                              (if (equal (nth numero-variavel dominio) (list 0))
                                  (setf (nth numero-variavel dominio) (list 0 1)))))
                    (push (faz-restricao posicoes-adjacentes (aref array i j) (list tamanho-linha tamanho-coluna)) restricoes)))))) (values dominio (nreverse restricoes))))
                            

;parte 2.2.1
(defun fill-a-pix->psr (arr)
  (multiple-value-bind (dominio restricoes) (cria-dominio-restricao arr) (cria-psr (cria-lista-variaveis arr) dominio restricoes)))

(defun psr->fill-a-pix (psr linhas colunas)
  (let ((arr (make-array (list linhas colunas))) ; cria um array do tamanho especificado
        (variaveis (psr-variaveis-todas psr)))
    (do ((i 0 (+ i 1)) ; ciclo que percorre as linhas do array
         (counter 0))
       ((= i linhas)) 
     (do ((j 0 (+ j 1))) ; ciclo que percorre as colunas do array
        ((= j colunas))
      (setf (aref arr i j) (psr-variavel-valor psr (nth counter variaveis))) ; adicionar variavel a posicao i j da matrix
      (setf counter (+ counter 1))))                                         ; incrementar contador de variavel               
  arr)) 

;parte 2.2.2
(defun procura-retrocesso-simples (psr)
  (let ((testesTotais 0)
        (variavel nil))
   (if (psr-completo-p psr)
       (values psr testesTotais)
       (progn
         (setf variavel (first (psr-variaveis-nao-atribuidas psr)))
         (dolist (valor (psr-variavel-dominio psr variavel) (values nil testesTotais)) ; retorna nil se acabar o dolist sem haver chamada de return
           (multiple-value-bind (valor-consistente testes) (psr-atribuicao-consistente-p psr variavel valor)
             (setf testesTotais (+ testesTotais testes)) ; contar sempre todos os testes feitos
             (if valor-consistente                       ; se o elemento do dominio for consistente, passar a proxima variavel com uma chamada de procura-retrocesso-simples
                 (progn
                   (psr-adiciona-atribuicao! psr variavel valor)
                   (multiple-value-bind (resultado maisTestes) (procura-retrocesso-simples psr)
                     (setf testesTotais (+ testesTotais maisTestes))
                     (if resultado (return (values resultado testesTotais))) ; se resultado nao for nil, sair do loop e devolver resultado
                     (psr-remove-atribuicao! psr variavel))))))))))

(defun resolve-simples (arr)
  (let ((psr nil)
        (array-final nil)
        (resultado nil)
        (tamanho (array-dimensions arr)))
   (setf psr (fill-a-pix->psr arr))
   (setf resultado (procura-retrocesso-simples psr))
   (if resultado (setf array-final (psr->fill-a-pix psr (first tamanho) (second tamanho))))
   array-final))
  
 ;; o^2?
 ;; devolve a variavel com grau maior
(defun heuristica-grau (psr)
  (let ((variavel-resultado nil)
        (variavel-resultado-grau -1)
        (variaveis (psr-variaveis-nao-atribuidas psr))); para evitar erros quando a lista de restricoes comuns tem length 0
    (if (= (length variaveis) 1)
        (setf variavel-resultado (first variaveis))
        (progn
          (dolist (variavel variaveis)
            (let ((variavel-restricoes (psr-variavel-restricoes psr variavel))
                  (lista-restricoes-comuns nil))
              (dolist (variavel2 variaveis)
                (if (not (equal variavel2 variavel))
                    (setf lista-restricoes-comuns (append lista-restricoes-comuns (procura-restricoes-comuns variavel-restricoes variavel2))))) ; procura restricoes comuns com outras variaves nao atribuidas
              (setf lista-restricoes-comuns (remove-duplicates lista-restricoes-comuns :test 'eq)) ;; no final de ter todas as restricoes comuns com as outras variaveis, remove todos os elementos repetidos
              (if (> (length lista-restricoes-comuns) variavel-resultado-grau)                     ;; se for um elemento com mais restricoes do que os previamente testados
                  (progn (setf variavel-resultado variavel) (setf variavel-resultado-grau (length lista-restricoes-comuns)))))))) ;; guardar variavel e grau da variavel
   variavel-resultado))
   
(defun procura-retrocesso-grau (psr)
  (let ((testesTotais 0)
        (variavel nil))
   (if (psr-completo-p psr)
       (values psr testesTotais)
       (progn
         (setf variavel (heuristica-grau psr)) ; unica diferenca da procura simples, usa heuristica para encontrar proxima variavel a ser instanciada
         (dolist (valor (psr-variavel-dominio psr variavel) (values nil testesTotais)) ; retorna nil se acabar o dolist sem haver chamada de return
           (multiple-value-bind (valor-consistente testes) (psr-atribuicao-consistente-p psr variavel valor)
             (setf testesTotais (+ testesTotais testes)) ; contar sempre todos os testes feitos
             (if valor-consistente                       ; se o elemento do dominio for consistente, passar a proxima variavel com uma chamada de procura-retrocesso-simples
                 (progn
                   (psr-adiciona-atribuicao! psr variavel valor)
                   (multiple-value-bind (resultado maisTestes) (procura-retrocesso-grau psr)
                     (setf testesTotais (+ testesTotais maisTestes))
                     (if resultado (return (values resultado testesTotais))) ; se resultado nao for nil, sair do loop e devolver resultado
                     (psr-remove-atribuicao! psr variavel))))))))))

(defun heuristica-mrv (psr)
  (let* ((variaveis (psr-variaveis-nao-atribuidas psr))
         (variavel-resultado (first variaveis))
         (dominio-variavel-resultado (length (psr-variavel-dominio psr variavel-resultado))))
    (dolist (variavel (rest variaveis))
      (if (< (length (psr-variavel-dominio psr variavel)) dominio-variavel-resultado)
          (progn (setf variavel-resultado variavel) (setf dominio-variavel-resultado (length (psr-variavel-dominio psr variavel))))))
  variavel-resultado))

(defun procura-retrocesso-fc-mrv (psr)
  (let ((testesTotais 0)
       (variavel nil))
     (if (psr-completo-p psr)
         (values psr testesTotais)
         (progn
           (setf variavel (heuristica-mrv psr))
           (dolist (valor (psr-variavel-dominio psr variavel) (values nil testesTotais)) ;; return final
             (multiple-value-bind (valor-consistente testes) (psr-atribuicao-consistente-p psr variavel valor)
               (setf testesTotais (+ testesTotais testes))
               (if valor-consistente
                   (progn
                     (psr-adiciona-atribuicao! psr variavel valor)
                     (multiple-value-bind (inferencias testes2) (forward-checking psr variavel)
                     (incf testesTotais testes2)
                       (if inferencias
                           (progn
                             (let ((dominios nil))
                               (dolist (inf inferencias)
                                 (setf dominios (cons (cria-inferencia (inferencia-var inf) (psr-variavel-dominio psr (inferencia-var inf))) dominios))
                                 (psr-altera-dominio! psr (inferencia-var inf) (inferencia-dominio inf)))
                               (multiple-value-bind (resultado testes3) (procura-retrocesso-fc-mrv psr)
                                 (incf testesTotais testes3)
                                 (if resultado
                                     (return (values resultado testesTotais))))
                               (dolist (inf dominios) ;; repor valores no dominio
                                 (psr-altera-dominio! psr (inferencia-var inf) (inferencia-dominio inf)))))))
                     (psr-remove-atribuicao! psr variavel)))))))))
                   
                     
                     
                     
(defun arcos-vizinhos-nao-atribuidos (psr variavel)
  (let ((lista-arcos nil))
    (dolist (var-natribuida (psr-variaveis-nao-atribuidas psr))
      if (null (equal variavel var-natribuida))
         (progn (if (procura-restricoes-comuns  (psr-variavel-restricoes psr variavel) var-natribuida)
                    (setf lista-arcos (nconc lista-arcos (list (cons var-natribuida variavel)))))))
    lista-arcos))
       
                    
(defun forward-checking (psr variavel)
  (let ((testesTotais 0)
        (inferenciasFinais nil)
        (lista-arcos (arcos-vizinhos-nao-atribuidos psr variavel)))
        
    (dolist (arco lista-arcos (values inferenciasFinais testesTotais)) ; return no fim de todos os ciclos
      (multiple-value-bind (revise-result testes inferencias) (revise psr (car arco) (cdr arco) inferenciasFinais)
        (incf testesTotais testes)
	    (setf inferenciasFinais inferencias)
        (if revise-result
            (let ((dominio (inferencia-dominio (procura-variavel-inferencia-lista (car arco) inferencias))))
              (if (null dominio)
                  (return (values nil testesTotais)))))))))            
      
(defun revise (psr x y inferencias)
  (let ((testesTotais 0)
         (revised nil)
         (dominio-x nil)     
         (novo-dominio-x nil)
         (dominio-y nil)
         (lista-inferencias inferencias))
    (multiple-value-bind (inferencia-x) (procura-variavel-inferencia-lista x lista-inferencias)
       (if inferencia-x
           (setf dominio-x (inferencia-dominio inferencia-x))
           (setf dominio-x (psr-variavel-dominio psr x))))
    (setf novo-dominio-x dominio-x)
    (multiple-value-bind (valor-y) (psr-variavel-valor psr y)
       (if valor-y
           (setf dominio-y (list valor-y))
           (progn
             (multiple-value-bind (inferencia-y) (procura-variavel-inferencia-lista y lista-inferencias)
               (if inferencia-y
                   (setf dominio-y (inferencia-dominio inferencia-y))
                   (setf dominio-y (psr-variavel-dominio psr y)))))))
    (dolist (vx dominio-x)
      (let ((foundConsistentValue nil))
        (dolist (vy dominio-y)
            (multiple-value-bind (valor-consistente testes) (psr-atribuicoes-consistentes-arco-p psr x vx y vy)
               (incf testesTotais testes)
               (if valor-consistente
                   (progn (setf foundConsistentValue t)
                          (return)))))
        (if (null foundConsistentValue)
            (progn
              (setf revised t)
              (delete vx novo-dominio-x)))))
    (if revised
        (setf lista-inferencias (adiciona-inferencia-lista (cria-inferencia x novo-dominio-x) lista-inferencias)))
   (values revised testesTotais lista-inferencias)))
        
;; tipo inferencia
(defun cria-inferencia (var dominio)
  (list var dominio))

(defun inferencia-var (inferencia)
  (first inferencia))

(defun inferencia-dominio (inferencia)
  (second inferencia))
  
(defun inferencia-variavel-igual-p (inf1 inf2)
  (equal (first inf1) (first inf2)))

(defun variavel-inferencia-p (var inf)
  (equal var (first inf)))

(defun procura-variavel-inferencia-lista (var lista)
  (multiple-value-bind (n) (position var lista :test 'variavel-inferencia-p)
    (if n
        (nth n lista)
        nil)))

;; devolve lista, pode destruir lista passada
(defun adiciona-inferencia-lista (inf lista)
  (let ((lista-resultado lista))
    (multiple-value-bind (posicao) (position inf lista :test 'inferencia-variavel-igual-p)
      (if posicao
          (progn (setf (nth posicao lista-resultado) inf)
                 lista-resultado)
          (cons inf lista-resultado)))))

;this way it works in whatever implementation
#+clisp (load "exemplos.fas")
#+sbcl (load "exemplos.fasl")
