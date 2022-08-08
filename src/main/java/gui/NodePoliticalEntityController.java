package gui;

import java.net.URL;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Label;
import politics.Candidate;
import politics.Party;
import politics.PoliticalEntity;

public class NodePoliticalEntityController implements Initializable {
	
	private final PoliticalEntity e;
	
    @FXML
    private Label labelAffiliazione;

    @FXML
    private Label labelNome;
    
    public NodePoliticalEntityController(PoliticalEntity e) {
    	this.e = Objects.requireNonNull(e);
    }
    
	@Override
	public void initialize(URL location, ResourceBundle resources) {
		if(e instanceof Party) {
			labelNome.setText(((Party)e).getName());
			labelAffiliazione.setText("");
		} else if(e instanceof Candidate) {
			Candidate c = (Candidate)e;
			labelNome.setText(c.getName() + " " + c.getSurname());
			labelAffiliazione.setText(c.getParty().getName());
		} else {
			throw new IllegalArgumentException("Tipo di votazione non supportato.");
		}
	}

}