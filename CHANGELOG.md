# Changelog — Mineirart Lagos

Formato: uma entrada por versão, máx 2 linhas.

---

## v1.22
Contador de alertas não lidos no sidebar (prazos + notificações somados). Notificação só é marcada como lida ao clicar na linha inteira; visual diferenciado para itens não lidos.

## v1.21
Grava `completed_by` e `completed_at` ao concluir tarefa. Exibe "Concluída por [nome]" no card do Kanban, na lista Minhas Tarefas e no modal de detalhe.

## v1.20
Corrige cor do texto de linhas recolhidas nas notas de área para legibilidade normal (estava escuro demais após o toggle).

## v1.19
Adiciona seta `←` nas linhas de notas de área com toggle de recolher/expandir e suporte a reordenamento por arrastar.

## v1.18
Corrige descrição de limites do sistema na tela de Administração. Sincroniza versão no CLAUDE.md.

## v1.17
Adiciona notificação de comentário com preview do texto para todos os participantes da tarefa (responsáveis, criador e membros da área).

## v1.16
Corrige sincronização de anotações mensais no módulo de Performance.

## v1.15
Introduz backup rotativo obrigatório: app(1).js sempre guarda a versão anterior de app.js antes de qualquer modificação.

## v1.14
Corrige visibilidade da data de criação nos cards do Kanban.

## v1.13
Exibe data de criação relativa (ex: "há 2 dias") nas tarefas com tooltip mostrando data/hora absoluta.

## v1.12
Ordena tarefas "Em Andamento" antes de "A Fazer" na página Minhas Tarefas.

## v1.11
Separa tarefas ativas e concluídas em seções distintas na página Minhas Tarefas.

## v1.10
Ajustes internos de versão e correções de encoding no CLAUDE.md.

## v1.9
Iguala fonte dos chips do Calendário de Prospecção ao Calendário principal.

## v1.4 – v1.8
Versões iniciais: estrutura base do app, áreas, Kanban, calendários, organograma e fluxograma.
