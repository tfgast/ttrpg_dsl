use ratatui::buffer::Buffer;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Paragraph};
use ratatui::Frame;

use crate::map::{EntityDisplay, Map, Tile};

// ── Rendering ───────────────────────────────────────────────────

pub fn draw(frame: &mut Frame, map: &Map, entities: &[EntityDisplay], messages: &[String]) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Min(map.height as u16 + 2), // map + border
            Constraint::Length(6),                   // message log
        ])
        .split(frame.area());

    draw_map(frame, chunks[0], map, entities);
    draw_messages(frame, chunks[1], messages);
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
    if ent.is_player {
        Style::default().fg(Color::Yellow)
    } else {
        Style::default().fg(Color::Red)
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
