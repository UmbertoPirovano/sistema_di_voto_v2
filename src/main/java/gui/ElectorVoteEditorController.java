package gui;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.input.MouseEvent;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import politics.Candidate;
import politics.Party;
import politics.PoliticalEntity;
import polls.Poll;
import polls.PollCategorico;
import polls.PollOrdinale;
import polls.PollReferendum;
import system.SystemEvote;
import users.Elector;

public class ElectorVoteEditorController implements Initializable{
	
	private final Poll p;	
	private Map<Node, PoliticalEntity> nodeDictionary;

    @FXML
    private Label labelVotazione;

    @FXML
    private Button logoutButton;

    @FXML
    private Text nameSurnameLabel;
    
    @FXML
    private ListView<Node> candidateList;

    @FXML
    private ListView<Node> selectedList;

    @FXML
    private Button submitButton;

    @FXML
    private Text usernameLabel;
    
    @FXML
    void confirmVote(ActionEvent event) {
    	try {
    		List<PoliticalEntity> vote = generateVote();
    		validateVote(vote);
    		showVoteReviewInterface(vote);
    	} catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
    }

    @FXML
    void logout(ActionEvent event) {
    	SystemEvote.getInstance().logout();
    	showLoginWindow();
    }
    
    public ElectorVoteEditorController(Poll p) {
    	System.out.println("Creating vote window...");
    	this.p = Objects.requireNonNull(p);
    	this.nodeDictionary = new HashMap<Node, PoliticalEntity>();
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		System.out.println("Initializing vote window...");
		Elector e = (Elector)SystemEvote.getInstance().getSession().getUser();
		nameSurnameLabel.setText(e.getName() + " " + e.getSurname());
		usernameLabel.setText(e.getUsername());
		labelVotazione.setText(p.getName());
		populateList();
	}
	
	private Iterator<PoliticalEntity> loadCandidates() {
		if(p instanceof PollReferendum) {
			Party yes = new Party("Si'");
			Party no = new Party("No");
			List<PoliticalEntity> politics = new ArrayList<PoliticalEntity>();
			politics.add(yes);
			politics.add(no);
			return politics.iterator();
		} else if(p instanceof PollOrdinale) {
			return ((PollOrdinale)p).getCandidates();
		} else if(p instanceof PollCategorico) {
			return ((PollCategorico)p).getAllCandidates();
		} else {
			throw new IllegalArgumentException("Tipo di votazione non supportato.");
		}
	}
	
	private void populateList() {
		List<PoliticalEntity> politics = new ArrayList<>();
		Iterator<PoliticalEntity> it = loadCandidates();
		
		while(it.hasNext()) {
			politics.add(it.next());
		}
		
		for(PoliticalEntity e : politics) {
			try {
				FXMLLoader loader = new FXMLLoader(getClass().getResource("NodePoliticalEntity.fxml"));
				NodePoliticalEntityController controller = new NodePoliticalEntityController(e);
				loader.setController(controller);
				final Node n = loader.load();
				nodeDictionary.put(n, e);
				
				n.setOnMouseClicked(new EventHandler<MouseEvent>() {
					@Override
					public void handle(MouseEvent event) {
						if(candidateList.getItems().contains(n)) {
							selectedList.getItems().add(n);
							candidateList.getItems().remove(n);
						}else if(selectedList.getItems().contains(n)) {
							selectedList.getItems().remove(n);
							candidateList.getItems().add(n);
						}
					}					
				});
				candidateList.getItems().add(n);
			}catch(IOException exc){
				showErrorMessage("errore nella generazione dei nodi\n" + exc.getMessage());
			}
			
		}
	}
	
	/**
	 * Restituisce la lista contenente le entita' politiche selezionate rispettando
	 * l'odine in cui sono state selezionate.
	 */
	private List<PoliticalEntity> generateVote() {
		List<PoliticalEntity> vote = new ArrayList<PoliticalEntity>();
		List<Node> selected = selectedList.getItems();
		for(int i=0 ; i < selected.size() ; i++) {
			PoliticalEntity e = nodeDictionary.get(selected.get(i));
			vote.add(e);
		}
		return vote;
	}
	
	private void validateVote(List<PoliticalEntity> vote) throws Exception{
		if(p instanceof PollReferendum) {
			if(vote.size() > 1) {
				throw new IllegalArgumentException("Puoi fare solo una scelta.");
			}
		} else if(p instanceof PollOrdinale) {
			//non mi vengono in mente vincoli
		} else if(p instanceof PollCategorico) {
			Party party = null;
			for(PoliticalEntity e : vote) {
				if(e instanceof Party) {
					Party tmp = (Party)e;
					if(party == null) {
						party = tmp;
					} else if(!party.equals(tmp)) {
						throw new IllegalArgumentException("Voto disgiunto non consentito");
					}
				}else if(e instanceof Candidate) {
					Candidate tmp = (Candidate)e;
					if(party == null) {
						party = tmp.getParty();
					} else if(!party.equals(tmp.getParty())) {
						throw new IllegalArgumentException("Voto disgiunto non consentito");
					}
				}
			}
		} else {
			throw new IllegalArgumentException("");
		}
	}
	
	private void showLoginWindow() {
		try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("LoginWindow.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Login");
        	stage.setScene(new Scene(root, 500, 390));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}
	
	private void showErrorMessage(String s) {
		Objects.requireNonNull(s);
		String msg = "ERROR:\n\n";
		msg += s;
		try {
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(msg);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("ERROR");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}
	
	private void showVoteReviewInterface(List<PoliticalEntity> v) {
		Objects.requireNonNull(v);
		try {
    		FXMLLoader loader = new FXMLLoader(getClass().getResource("ElectorVoteReview.fxml"));
    		ElectorVoteReviewController controller = new ElectorVoteReviewController(p, v);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("Revisione voto");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			showErrorMessage(e.getMessage());
		}
		submitButton.getScene().getWindow().hide();
	}
}

