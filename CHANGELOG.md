# Changelog — Mineirart Lagos

Formato: uma entrada por versão, máx 2 linhas.

---

## v1.30
Badge numérico em "Minhas Tarefas" na sidebar para novas tarefas designadas ao usuário; some ao abrir a tarefa (clique no modal).

## v1.29
Alertas reúne cobranças de colegas (manual_alert) + prazos críticos; Atualizações fica exclusivo para comentários; badges e botões "Limpar" separados por tipo.

## v1.28
Nova aba "Atualizações" na sidebar (abaixo de Alertas) para notificações de comentários e alertas manuais; pop-ups restritos a alertas críticos (prazo próximo somente para responsável direto, alertas de colegas no carregamento).

## v1.27
Movimentação sincronizada de Macros no fluxograma: ao arrastar um bloco Macro, todos os filhos se movem em conjunto preservando posições relativas.

## v1.26
Remove notas (stickies) do fluxo e organograma; drag-drop de processo único em macro expandido; macros expandidos renderizados na frente dos demais blocos.

## v1.25
Fluxograma/organograma: macroprocessos expansíveis, seleção múltipla, criação de grupos, ordenação automática e arestas visíveis mesmo com macro recolhido.

## v1.24
Performance: dashboard exibe dados do localStorage imediatamente ao abrir, sem esperar resposta do Firebase. Firebase atualiza em seguida em background.

## v1.23
Corrige dashboard do Performance não aparecer no primeiro clique: impede que listeners Firebase recriem o iframe enquanto ele já está carregando.

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
