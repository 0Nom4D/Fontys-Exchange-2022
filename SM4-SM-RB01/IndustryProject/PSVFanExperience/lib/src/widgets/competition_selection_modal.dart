import 'package:flutter/material.dart';
import 'package:psv_fan_experience/src/models/competitions.dart';

class CompetitionSelectionModal extends StatelessWidget {
  const CompetitionSelectionModal({super.key});

  @override
  Widget build(BuildContext context) {
    return Container(
      decoration: const BoxDecoration(
        borderRadius: BorderRadius.only(
          topLeft: Radius.circular(10.0),
          topRight: Radius.circular(10.0),
        ),
      ),
      height: MediaQuery.of(context).size.height * .5,
      child: Column(
        children: [
          ListTile(
            title: const Text(
              "Choose a competition",
              textAlign: TextAlign.center,
              style: TextStyle(color: Colors.black)
            ),
            shape: const RoundedRectangleBorder(
              borderRadius: BorderRadius.only(
                topLeft: Radius.circular(10.0),
                topRight: Radius.circular(10.0),
              ),
            ),
            tileColor: Theme.of(context).colorScheme.tertiary,
          ),
          SizedBox(
            height: MediaQuery.of(context).size.height * .42,
            child: ListView.separated(
              itemBuilder: (context, index) => Competition.competitions[index].locationRestriction != null
                ? FutureBuilder(
                    future: Competition.competitions[index].locationRestriction!(),
                    builder: (BuildContext context, AsyncSnapshot<bool> snapshot) {
                      if (snapshot.hasData) {
                        return ListTile(
                          title: Text(
                            Competition.competitions[index].name,
                            textAlign: TextAlign.center,
                            style: const TextStyle(color: Colors.black)
                          ),
                          trailing: snapshot.data == false ? const Icon(Icons.lock) : null,
                          onTap: snapshot.data == false ? null : () => Navigator.pop(context, Competition.competitions[index].name)
                        );
                      }
                      return const SizedBox(width: 25, height: 25, child: CircularProgressIndicator());
                    },
                  )
              : Competition.competitions[index].timeRestriction != null
                ? ListTile(
                  title: Text(
                    Competition.competitions[index].name,
                    textAlign: TextAlign.center,
                    style: const TextStyle(color: Colors.black)
                  ),
                  trailing: !Competition.competitions[index].timeRestriction!() ? const Icon(Icons.lock) : null,
                  onTap: !Competition.competitions[index].timeRestriction!() ? null : () => Navigator.pop(context, Competition.competitions[index].name)
                )
                : ListTile(
                  title: Text(
                    Competition.competitions[index].name,
                    textAlign: TextAlign.center,
                    style: const TextStyle(color: Colors.black)
                  ),
                  onTap: () => Navigator.pop(context, Competition.competitions[index].name)
              ),
              separatorBuilder: (context, index) => const Divider(),
              itemCount: Competition.competitions.length
            ),
          ),
        ],
      ),
    );
  }
}