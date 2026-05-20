# Regras do projeto Mineirart Lagos

- Nunca use worktrees. Edite os arquivos diretamente nesta pasta.
- Sempre modifique apenas o arquivo js/app.js
- A cada modificacao, incremente a versao no formato v1.x (atual: v1.22)
- Sempre atualize o numero da versao tambem dentro do js/app.js, na linha do topbar onde aparece ex: v1.12 (buscar por "v1." no arquivo para localizar)
- Mensagem de commit no formato: feat: descricao da mudanca (v1.x)
- Faca commit e push sempre na branch main

- Sempre execute git pull antes de iniciar qualquer modificacao

## Backup rotativo de app.js
Antes de qualquer modificacao em js/app.js, executar obrigatoriamente:
1. Deletar js/app(1).js (se existir)
2. Copiar js/app.js atual para js/app(1).js
3. Fazer a modificacao em js/app.js
4. Commitar ambos: js/app.js e js/app(1).js
O repositorio deve sempre ter exatamente esses dois arquivos: o atual (app.js) e o anterior (app(1).js).

- A versao segue o formato v1.x onde x incrementa de 1 em 1 (ex: v1.9 -> v1.10 -> v1.11). Nunca use v2.0

## Changelog
A cada modificacao em js/app.js, adicionar obrigatoriamente uma entrada no topo de CHANGELOG.md (abaixo da linha de separacao `---`), no formato:

## v1.x
[max 2 linhas compactas descrevendo o que foi alterado ou inserido]

Commitar CHANGELOG.md junto com js/app.js e js/app(1).js no mesmo commit.
