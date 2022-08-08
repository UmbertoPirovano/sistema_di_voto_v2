package gui;

import java.util.Objects;

import javafx.beans.property.SimpleStringProperty;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.TableView;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import politics.Candidate;
import politics.Party;
import politics.PoliticalEntity;

public class RowPoliticalEntity {
	private final PoliticalEntity e;
	private final TableView<RowPoliticalEntity> tv;
	private final SimpleStringProperty party;
	private final SimpleStringProperty candidate;
	private ButtonBar buttonBar;
	
	public RowPoliticalEntity(PoliticalEntity e, TableView<RowPoliticalEntity> tv) {
		this.e = Objects.requireNonNull(e);
		this.tv = Objects.requireNonNull(tv);
		if(e instanceof Party) {
			Party p = (Party) e;
			party = new SimpleStringProperty(p.getName());
			candidate = new SimpleStringProperty("-");
		} else if(e instanceof Candidate) {
			Candidate c = (Candidate) e;
			party = new SimpleStringProperty(c.getParty().getName());
			candidate = new SimpleStringProperty(c.getName() + " " + c.getSurname());
		} else {
			throw new IllegalArgumentException("Tipo di entità politica non supportato.");
		}
		
		Button deleteButton = new Button();
		ImageView deletePng = new ImageView(new Image(getClass().getResource("delete.png").toString()));
		deletePng.setFitHeight(20);
		deletePng.setPreserveRatio(true);
		deleteButton.setGraphic(deletePng);
		deleteButton.setOnAction(event -> handleDeleteAction());
		
		buttonBar = new ButtonBar();
		buttonBar.getButtons().addAll(deleteButton);
	}
	
	private void handleDeleteAction() {
		tv.getItems().remove(this);
	}
	
	public PoliticalEntity getPoliticalEntity() {
		return e;
	}
	
	public String getParty() {
		return party.get();
	}
	
	public String getCandidate() {
		return candidate.get();
	}
	
	public ButtonBar getButtonBar() {
		return buttonBar;
	}
}
