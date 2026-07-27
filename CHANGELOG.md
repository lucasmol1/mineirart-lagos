# Changelog — Mineirart Lagos

Formato: uma entrada por versão, máx 2 linhas.

---

## v1.65
Anexo em tarefas/eventos agora aceita PDF (além de imagem) e pode ser feito direto na tela de Detalhe, sem precisar clicar em Editar. Continua limitado a 1 arquivo, com limite de tamanho, para preservar o espaço gratuito.

## v1.64
Nova aba Lixeira: guarda as últimas 10 tarefas/eventos excluídos com botão de restaurar. Cobre Calendário, Cal. Prospecção e agendamentos.

## v1.63
Acesso a uma área agora é herdado por todas as subáreas dela (ex: quem tem permissão em "Comercial" vê e é listado em "Mkt"). Corrige checagens de permissão inconsistentes em atribuição de tarefas, membros e notificações.

## v1.62
Duplo clique em um bloco do Fluxograma abre seus detalhes, editáveis por qualquer usuário. Alterações ficam registradas no histórico de ações.

## v1.61
Tarefas e eventos agora aceitam anexar 1 foto (arraste ou clique). Ao concluir uma tarefa, a foto anexada é apagada automaticamente para economizar espaço.

## v1.60
Corrige causa raiz do erro ao editar bloco do organograma: campos w/h ficavam `undefined` para blocos nunca redimensionados, e o Firebase rejeita esse valor no set().

## v1.59
Corrige edição de blocos no Organograma: quando o salvamento falhava (limite de escritas ou erro), o sistema mostrava "Salvo!" mesmo sem gravar. Agora exibe erro real e mantém o modal aberto.

## v1.58
Nova aba "Cotação de Frete": cadastro de freteiros (cubagem, valor do ajudante, tabela de preços por cidade) com importação via planilha (.xlsx/.csv), e comparador que ordena o custo total por destino.

## v1.57
Notificação de tarefa atrasada agora substitui a anterior da mesma tarefa em vez de acumular — mantém só a mais recente na aba Atualizações.

## v1.56
Responsáveis de tarefas divididos em FYA (For Your Action — quem deve agir) e FYI (For Your Information — quem deve saber), com chips coloridos e campos separados no modal e no detalhe.

## v1.55
Rebranding visual: paleta alinhada ao site mineirart.com.br (accent âmbar #f0a848 + fundo dark warm + detalhe vinho #5d1200). Status "Em Andamento" agora azul (#4a9ee8) e "Concluído" verde (#4ae89c).

## v1.54
Separa aba "Automáticas" em "Tarefas" (só some quando concluída) e "Eventos" (informativo, "Limpar tudo" descarta para sempre).

## v1.53
Adiciona abas superiores em Atualizações (Todas, Menções, Comentários, Automáticas) com contadores e não lidas.

## v1.52
Cria secao separada "Menções" em Atualizações e renomeia "Lembretes de ações de tarefas" para "Lembretes Ações".

## v1.51
Renomeia secao "Cobrancas de colegas" para "Lembretes de acoes de tarefas" na pagina de Alertas.

## v1.50
Corrige deteccao de mencao em comentarios antigos (sem flag salva), aplicando o destaque visual tambem por texto da mensagem.

## v1.49
Notificações de menção em comentários agora têm destaque visual (selo "Você foi mencionado", borda e ícone diferenciados).

## v1.48
Removida a aba secreta do gorila (ícone 🦍) e sua página com foto, presentes apenas para adm master.

## v1.47
Clique em notificação da aba Atualizações abre detalhe da tarefa; botão "Ver tarefa →" destacado.
Suporte a @menção em comentários: dropdown de usuários ao digitar @, destaque visual e notificação ao mencionado.

## v1.46
Adiciona opção secreta 🦍 na sidebar (visível apenas para adm master), exibindo a foto do gorila em tela cheia.

## v1.45
Separa aba Atualizações em duas seções: 💬 Comentários (só dispensável individualmente) e ⏰ Automáticas (tarefas/eventos atrasados, com "Limpar todas" próprio).

## v1.44
Adiciona botão "🗑️ Limpar tudo" no cabeçalho da aba Atualizações, visível imediatamente sem precisar rolar a página.

## v1.43
Adiciona botão "Marcar todas como lidas" na aba Atualizações (marca todos os tipos: comentários, tarefas e eventos atrasados). Corrige "Limpar todas" para apagar todos os tipos de notificação, não só comentários.

## v1.42
Corrige barra lateral colorida e handles de conexão no organograma: todos usam agora nW/nH (tamanho real do bloco) em vez dos valores padrão fixos W/H, acompanhando o resize.

## v1.41
Logout automático em tempo real quando o admin remove um usuário: o listener do próprio perfil detecta a remoção e chama signOut imediatamente.

## v1.40
Auto-marca como lidas notificações de comentário com mais de 7 dias ao abrir Atualizações, eliminando acúmulo histórico no badge.

## v1.39
Prospecção restrita ao admin master (isAdmin1); backup completo passa a incluir prosp_leads; barra de uso de leads adicionada ao painel Admin com legenda de bloqueio.

## v1.38
Módulo Prospecção & Follow-up Comercial: nova aba "📅 Prospecção" (rota prospeccao) com gestão de leads CRM, mini calendário de follow-ups, cards com urgência, estatísticas do pipeline e modal de criação/edição (path Firebase: prosp_leads/).

## v1.37
Calendário filtra por áreas onde o usuário é membro; push de eventos de calendário atrasados na aba Atualizações (⏰ throttle 5h); fluxograma: select "Macro" na toolbar para criar processos já dentro de um macroprocesso.

## v1.36
Notificação de tarefa atrasada na aba Atualizações: ao abrir o app, tarefas vencidas onde o usuário é responsável geram notificação ⏰ com borda vermelha, com throttle de 5h por tarefa via localStorage.

## v1.35
Handle de resize `<>` (22×22) no canto inferior direito de blocos do organograma e fluxograma; drop de grupo/bloco em container root funciona mesmo sem expandir antes; permissões de área viram somente leitura para usuários com manageAreas.

## v1.34
Avatar do criador exibido no canto inferior direito de cada nota (Notas, FYI global e FYI de área): bolinha com inicial + cor do usuário, tooltip com nome completo ao hover.

## v1.33
Membros da área: linha clicável "👥 Membros (N)" abaixo dos detalhes da área — expande/recolhe painel inline com avatar + nome de cada membro.

## v1.32
Exibe todos os responsáveis que concluíram no card e no modal: para tarefas multi-responsável, "Concluída por" lista todos os que marcaram como feito (via completions), não só o último.

## v1.31
Corrige badge de Alertas zerado: passa a contar todos os níveis de prazo (warn-1 a warn-3), não só os críticos de 24h.

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
