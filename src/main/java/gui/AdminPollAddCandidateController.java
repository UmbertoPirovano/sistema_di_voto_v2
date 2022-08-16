package gui;

import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.Initializable;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;
import javafx.scene.control.cell.PropertyValueFactory;
import politics.Candidate;
import politics.Party;
import politics.PoliticalEntity;
import polls.Poll;
import polls.PollCategorico;
import polls.PollOrdinale;
import system.SystemEvote;

public class AdminPollAddCandidateController implements Initializable {
	
    @FXML
    private Button addButton;

    @FXML
    private TableView<RowPoliticalEntity> candidatesTable;

    @FXML
    private TableColumn<RowPoliticalEntity, ButtonBar> colAction;

    @FXML
    private TableColumn<RowPoliticalEntity, String> colCandidate;

    @FXML
    private TableColumn<RowPoliticalEntity, String> colParty;

    @FXML
    private Button confirmButton;

    @FXML
    private TextField nameField;

    @FXML
    private TextField partyField;

    @FXML
    private TextField surnameField;
    
    private final Poll poll;
    private final boolean onlyParties;
    
    public AdminPollAddCandidateController(Poll poll, boolean onlyParties) {
    	this.poll = Objects.requireNonNull(poll);
    	this.onlyParties = onlyParties;
    	SystemEvote.getInstance().deletePoll(poll);
    }

    @FXML
    void handleAddButton(ActionEvent event) {
    	if(partyField.getText().isBlank())
    		return;	// se il campo 'party' non è compilato non fa nulla.
    	Party p = new Party(partyField.getText());
    	Candidate c = null;
    	if(!nameField.getText().isBlank() && !surnameField.getText().isBlank()) {
    		c = new Candidate(nameField.getText(), surnameField.getText(), p);
    	} else if((!nameField.getText().isBlank() && surnameField.getText().isBlank()) || (nameField.getText().isBlank() && !surnameField.getText().isBlank())) {
    		//se un campo tra 'name' e 'surname' è compilato ma l'altro no non fa nulla.
    		return;
    	}
    	if(c == null) {
    		addIfAbsent(p);
    	} else {
    		addIfAbsent(c);
    	}
    }
    
    /**
     * Aggiunge alla tabella una RowPoliticalEntity contenente e solamente
     * se e non è già contenuta in una delle RowPoliticalEntity già presenti.
     * @param e: l'istanza di PoliticalEntity che si vuole inserire nella tabella.
     * @return True se viene effettuato l'inserimento, False altrimenti.
     */
    private boolean addIfAbsent(PoliticalEntity e) {
    	Objects.requireNonNull(e);
    	for(RowPoliticalEntity re : candidatesTable.getItems()) {
    		if(re.getPoliticalEntity().equals(e)) return false;
    	}
    	candidatesTable.getItems().add(new RowPoliticalEntity(e, candidatesTable));
    	return true;
    }

    @FXML
    void handleConfirmButton(ActionEvent event) {
    	List<PoliticalEntity> candidates = new ArrayList<PoliticalEntity>();
    	for(RowPoliticalEntity re : candidatesTable.getItems()) {
    		candidates.add(re.getPoliticalEntity());
    	}
    	if(poll instanceof PollOrdinale) {
    		PollOrdinale p = ((PollOrdinale)poll);
    		p.addCandidate(candidates);
    		int size = 0;
    		Iterator<PoliticalEntity> it = p.getCandidates();
    		while(it.hasNext()) {
    			size++;
    			it.next();
    		}
    		System.out.println("Adding tot candidates to PollOrdinale: " + size);
    		SystemEvote.getInstance().addPoll(p);
    	} else if(poll instanceof PollCategorico){
    		PollCategorico p = ((PollCategorico) poll);
    		p.addCandidate(candidates);
    		int size = 0;
    		Iterator<Candidate> it = p.getCandidates();
    		while(it.hasNext()) {
    			size++;
    			it.next();
    		}
    		System.out.println("Adding tot candidates to PollCategorico: " + size);
    		SystemEvote.getInstance().addPoll(p);
    	}
    	confirmButton.getScene().getWindow().hide();    	
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		if(onlyParties) {
			nameField.setEditable(false);
			surnameField.setEditable(false);
		}
	
		colParty.setCellValueFactory(new PropertyValueFactory<>("party"));
		colCandidate.setCellValueFactory(new PropertyValueFactory<>("candidate"));
		colAction.setCellValueFactory(new PropertyValueFactory<>("buttonBar"));		
	}

}

