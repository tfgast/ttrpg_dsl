use ratatui::Frame;
use ratatui::buffer::Buffer;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Paragraph};

use crate::map::{EntityDisplay, Map, Tile};

// ── Stat line data ──────────────────────────────────────────────

/// A single formatted stat for the stats panel.
pub struct StatLine {
    pub label: String,
    pub text: String,
    /// For Bar display: (current, max). If present, a visual bar is drawn.
    pub bar: Option<(i64, i64)>,
}

// ── Rendering ───────────────────────────────────────────────────

pub fn draw(
    frame: &mut Frame,
    map: &Map,
    entities: &[EntityDisplay],
    messages: &[String],
    stats: &[StatLine],
) {
    let top_bottom = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Min(map.height as u16 + 2), // map row + border
            Constraint::Length(6),                  // message log
        ])
        .split(frame.area());

    // Split the top row into map (left) + stats panel (right)
    let top_cols = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Min(map.width as u16 + 2), // map + border
            Constraint::Length(22),                 // stats panel
        ])
        .split(top_bottom[0]);

    draw_map(frame, top_cols[0], map, entities);
    draw_stats(frame, top_cols[1], stats);
    draw_messages(frame, top_bottom[1], messages);
}

fn draw_map(frame: &mut Frame, area: Rect, map: &Map, entities: &[EntityDisplay]) {
    let block = Block::default().borders(Borders::ALL).title(" Dungeon ");
    let inner = block.inner(area);
    frame.render_widget(block, area);

    // Render map tiles + entities directly to the buffer
    let buf = frame.buffer_mut();
    render_map_to_buffer(buf, inner, map, entities);
}

fn render_map_to_buffer(buf: &mut Buffer, area: Rect, map: &Map, entities: &[EntityDisplay]) {
    for y in 0..map.height.min(area.height as usize) {
        for x in 0..map.width.min(area.width as usize) {
            let tile = map.get(x, y);
            let (ch, style) = tile_style(tile);

            let bx = area.x + x as u16;
            let by = area.y + y as u16;
            if let Some(cell) = buf.cell_mut((bx, by)) {
                cell.set_char(ch);
                cell.set_style(style);
            }
        }
    }

    // Draw entities on top
    for ent in entities {
        let ex = ent.x;
        let ey = ent.y;
        if ex < 0 || ey < 0 {
            continue;
        }
        let bx = area.x + ex as u16;
        let by = area.y + ey as u16;
        if bx >= area.x + area.width || by >= area.y + area.height {
            continue;
        }
        if let Some(cell) = buf.cell_mut((bx, by)) {
            cell.set_char(ent.glyph);
            cell.set_style(entity_style(ent));
        }
    }
}

fn tile_style(tile: Tile) -> (char, Style) {
    match tile {
        Tile::Floor => ('.', Style::default().fg(Color::DarkGray)),
        Tile::Wall => ('#', Style::default().fg(Color::Gray)),
    }
}

fn entity_style(ent: &EntityDisplay) -> Style {
    Style::default().fg(ent.color)
}

fn draw_stats(frame: &mut Frame, area: Rect, stats: &[StatLine]) {
    let block = Block::default().borders(Borders::ALL).title(" Stats ");
    let inner = block.inner(area);
    frame.render_widget(block, area);

    let bar_width = inner.width.saturating_sub(6) as usize; // space for "LBL "

    for (i, stat) in stats.iter().enumerate() {
        if i as u16 >= inner.height {
            break;
        }
        let y = inner.y + i as u16;

        let line = if let Some((cur, max)) = stat.bar {
            // Draw a bar: "HP 12/20 [████░░░░]"
            let label_val = format!("{} {}/{}", stat.label, cur, max);
            let filled = if max > 0 {
                ((cur.max(0) as u64 * bar_width as u64) / max as u64) as usize
            } else {
                0
            };
            let empty = bar_width.saturating_sub(filled);
            // Use two lines: value then bar
            // Actually keep it compact: label + fraction on one line
            let bar_str: String =
                "█".repeat(filled.min(bar_width)) + &"░".repeat(empty.min(bar_width));
            // Truncate bar to fit
            let max_w = inner.width as usize;
            if label_val.len() < max_w {
                let remaining = max_w - label_val.len() - 1;
                let bar_chars: String = bar_str.chars().take(remaining).collect();
                format!("{label_val} {bar_chars}")
            } else {
                label_val[..max_w].to_string()
            }
        } else {
            format!("{}: {}", stat.label, stat.text)
        };

        let spans = Line::from(Span::styled(line, Style::default().fg(Color::White)));
        let paragraph = Paragraph::new(spans);
        frame.render_widget(
            paragraph,
            Rect::new(inner.x, y, inner.width, 1),
        );
    }
}

fn draw_messages(frame: &mut Frame, area: Rect, messages: &[String]) {
    let block = Block::default().borders(Borders::ALL).title(" Log ");

    // Show last N messages that fit
    let inner_height = area.height.saturating_sub(2) as usize;
    let start = messages.len().saturating_sub(inner_height);
    let visible: Vec<Line> = messages[start..]
        .iter()
        .map(|m| Line::from(Span::raw(m.as_str())))
        .collect();

    let paragraph = Paragraph::new(visible).block(block);
    frame.render_widget(paragraph, area);
}
