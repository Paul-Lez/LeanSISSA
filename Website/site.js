// Enhance the tactic groups as tabs; without JavaScript both groups remain visible.
document.addEventListener('DOMContentLoaded', () => {
  const headings = [...document.querySelectorAll('main h2, article h2, section h2')];
  const elementary = headings.find(h => h.textContent.includes('Elementary tactics'));
  const advanced = headings.find(h => h.textContent.includes('More advanced automation'));
  if (!elementary || !advanced) return;
  const panels = [elementary.closest('section'), advanced.closest('section')];
  if (!panels[0] || !panels[1] || panels[0] === panels[1]) return;
  const bar = document.createElement('div');
  bar.className = 'tactic-tabs';
  bar.setAttribute('role', 'tablist');
  bar.setAttribute('aria-label', 'Tactic groups');
  const buttons = ['Elementary tactics', 'More advanced automation'].map((label, i) => {
    const button = document.createElement('button');
    button.type = 'button';
    button.textContent = label;
    button.id = `tactic-tab-${i}`;
    button.setAttribute('role', 'tab');
    panels[i].id ||= `tactic-panel-${i}`;
    button.setAttribute('aria-controls', panels[i].id);
    panels[i].setAttribute('role', 'tabpanel');
    panels[i].setAttribute('aria-labelledby', button.id);
    bar.append(button);
    button.addEventListener('click', () => select(i));
    button.addEventListener('keydown', event => {
      if (event.key === 'ArrowRight' || event.key === 'ArrowLeft') {
        event.preventDefault();
        const next = 1 - i;
        select(next);
        buttons[next].focus();
      }
    });
    return button;
  });
  function select(index) {
    panels.forEach((panel, i) => {
      panel.hidden = i !== index;
      buttons[i].setAttribute('aria-selected', String(i === index));
      buttons[i].tabIndex = i === index ? 0 : -1;
    });
  }
  panels[0].before(bar);
  function selectHash() {
    const id = decodeURIComponent(location.hash.slice(1));
    const target = id && document.getElementById(id);
    select(target && panels[1].contains(target) ? 1 : 0);
  }
  window.addEventListener('hashchange', selectHash);
  selectHash();
});

// Give diagnostics their own keyboard-accessible control. Verso embeds the
// messages in the highlighted code, where tactic hovers can obscure them.
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('code.hl.lean.block').forEach(block => {
    const errors = [...block.querySelectorAll('.has-info.error > .hover-container .verso-message.error')];
    if (!errors.length) return;

    const details = document.createElement('details');
    details.className = 'lean-errors';
    const summary = document.createElement('summary');
    summary.textContent = errors.length === 1 ? 'Show Lean error message' : 'Show Lean error messages';
    details.append(summary);
    errors.forEach(error => {
      const message = document.createElement('div');
      message.className = 'lean-error-message hl lean';
      const content = error.cloneNode(true);
      // IDs in the original message belong to the original goal view.
      content.querySelectorAll('[id]').forEach(element => element.removeAttribute('id'));
      content.querySelectorAll('[for]').forEach(element => element.removeAttribute('for'));
      message.append(content);
      details.append(message);
    });
    block.after(details);
  });
});
